# CoEndoYoneda and it's relation to Purity

CoYoneda related theorems and proofs deal with `SET`-valued functors of type `Functor C (SET ℓ)`
that, given an object `Z`, map an object `Y` to `Hom[ Z , Y ]`, the set of homomorphisms from `Z` to
`Y`, and map an homomorphism `z2y` to `Hom[ Z , Y ] → Hom[ Z , X ]`, the function composing `z2y`
with `y2x`.

Notice that I am dealing with **Co***Yoneda* related stuff, but I might as well have been dealing
with *Yoneda* related stuff.

CoYoneda related theorems are *pointful* and are the foundation of studying objects via
homomorphisms from them to other objects, switching from a pointful approach to a *pointfree*
approach.

*So I was wondering (having pointfree functional programming in mind)*

What if a functor of type `Functor (SET ℓ) C` exists as well? Such a functor maps functions to
homomorphisms, as in `PSBP`, where functions can be used as programs. 

In that case `SET`-valued functors of type `Functor C (SET ℓ)` can be composed with that functor of
type `Functor (SET ℓ) C`, obtaining an endofunctor of type `Functor C C` 
(and `SET ℓ` suddenly disappears (!)).

*Are there any pointfree* *Co**Endo**Yoneda* *theorems that can be formulated and proved?*

It turns out that this is possible for categories for which there exists a functor as above and for
which there also exist some simple extra `field`s and laws.

... notice that *simple* is not the same as *easy* ...

*So I was wondering (having pointfree functional programming in mind)*

*Which Categories can I use my theorems for?*

**I am deeply convinced that the best theory comes from practice.**

But, this time, I was way to curious about theory before thinking about practice. Of course, I hoped
that the theory could, somehow, be used for, *at least, some* class of computation-valued functions,
but no, it turned out that one of the extra `field`s with its law implied that the theory can only
be used for pure functions. 

So far for the bad news. But here is the good news.

*"every disadvantage has its advantage" a.k.a. "elk nadeel heb se voordeel"*

Who originally quoted this (or, at least a very similar) statement? 

It was **not** Johan Cruyff. 

<details>
  <summary>Who was it then?</summary>
  It was Willem van Hanegem
</details>

<br>

My extra constraint turned out, for computation-valued functions, to be *equivalent* with the
pureness of the computation involved. 

*So what is the big deal then?*

My formulation is a pointfree formulation of pureness of computation-valued function implementations
of homomorphisms in a simple way. 

I am aware that there exist "high-tech categorical" pointfree formulations of pureness, but they are
all beyond the scope of this presentation (and, frankly, beyond my capabilities). 

For information about *pointful* ways to formulate pureness, see, for example,
[idempotent monad in nLab](https://ncatlab.org/nlab/show/idempotent+monad).

It has a link to a book of Francis Borceux, from Belgium. By the way, the book was given to me by
Graham Hutton when I worked here in Utrecht with him, Erik Meyer and, of course, also Doaitse
Swierstra (our (so much more than a) boss). Graham estimated that I was better able to read that
book than he was (which wasn't entirely true, but anyway).

By now you probably have noticed that "pointfree closed component compositionality" is one of my
favorite topics.

### `import`s

We need to `import` some artifacts from the standard Agda and Cubical Agda libraries. 

```agda
{-# OPTIONS --cubical --guardedness #-}
module CoEndoYoneda where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
```

## Bijection

We encode a bijection as two functions, `from` and `to`, that are each other's inverses.

I have to double-check if I cannot use a standard library `record`.

```agda
record _⇿_ {ℓ ℓ' : Level} (Z : Type ℓ) (Y : Type ℓ') : Type (ℓ ⊔ ℓ') where
  field
    to : Z → Y
    from : Y → Z
    to_from : ∀ z → to (from z) ≡ z
    from_to : ∀ y → from (to y) ≡ y
```

## Basic Functional Category

We need some `import`s from the Cubical Categories library.

```agda
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets

open Functor
open NatTrans
```

Let's start with `BasicFunctionalCategory`.

`FF` (Functional Functor) is a functor from `SET ℓ` to `C`.

`CYF` is the CoYoneda embedding, a functor from `C` to `SET ℓ`.

`CYEF` is the composition of `FF` with `CYF`.

`T` is a terminal object in the category of sets and `tt*` is the unique element of `T`.

`G` (read as "global-like") is the CoYoneda endofunctor applied to `FF.F-ob T`.

`g` models global-like elements of `C` as homomorphisms from `FF.F-ob T` to `FF.F-ob Z`.

`η` is a "monad unit - like" natural transformation from the identity functor `Id` to `G`.

`η-eq-T` is an equational law dealing with `η` and `g`.

```agda
record BasicFunctionalCategory {ℓ : Level}

    (C : Category (lsuc ℓ) ℓ) 

    (FF : Functor (SET ℓ) C) : Type (lsuc ℓ) where

  private
    module C = Category C
    module FF = Functor FF

  open C

  CYF : ob → Functor C (SET ℓ)
  CYF Z = record
    { F-ob = λ Y → (C.Hom[ Z , Y ] , isSetHom)
    ; F-hom = λ y2x → (λ z2y → z2y ⋆ y2x)
    ; F-id = funExt ⋆IdR
    ; F-seq = λ y2x x2w → funExt (λ z2y → sym (⋆Assoc z2y y2x x2w))
    }

  CYEF : ob → Functor C C
  CYEF Z = FF ∘F (CYF Z)

  T : hSet ℓ
  T = (Unit* , isSetUnit*)

  G : Functor C C
  G = CYEF (FF.F-ob T)

  private
    module G = Functor G

  open G    

  g : {Z : hSet ℓ} → fst Z → Hom[ FF.F-ob T , FF.F-ob Z ]
  g = λ z → FF.F-hom (λ _ → z)

  field 
    η : NatTrans Id G
  
  field    
    η-eq-T : N-ob η (FF.F-ob T) ≡ g (g tt*)
```

Let's continue with `FunctionalCategory`.

## Functional Category

`μ` is a "monad multiplication - like" natural transformation from `G ∘F G` to `G`.

`η-eq` is a more general version of `η-eq-T`.

`idˡ` is the monadic left identity law dealing with `η` and `μ`. 

```agda
record FunctionalCategory 
    {ℓ : Level}
    (C : Category (lsuc ℓ) ℓ) 
    (FF : Functor (SET ℓ) C) : Type (lsuc ℓ) where
  private
    module C = Category C
    module FF = Functor FF

  open C
  open FF

  -- Inheritance by delegation to `bfc`
  field
    bfc : BasicFunctionalCategory C FF
  open BasicFunctionalCategory bfc public

  G∘G = G ∘F G

  field  
    μ : NatTrans G∘G G  

  field
    η-eq : ∀ {Z} → N-ob η (FF.F-ob Z) ≡ FF.F-hom g

  η-eq-T-from-η-eq : N-ob η (FF.F-ob T) ≡ g (g tt*)
  η-eq-T-from-η-eq = η-eq

  field
    idˡ : ∀ {Z} → N-ob η (F-ob G Z) ⋆ N-ob μ Z ≡ id
```

We are ready for our CoEndoYoneda theorem.

Our theorem is similar to the standard CoYoneda one.

Given an object `Z` and a `SET`-valued functor `F`, natural transformations of type
`NatTrans (CYF Z) F` are in one-to-one correspondence with objects of type
`F.F-ob Z`.

Here it is

Given an object `Z` and an endofunctor `EF`, natural transformations of type
`NatTrans (CYEF Z) (G ∘F EF)` are in one-to-one
correspondence with objects of type `(CYF ∘F (G ∘F EF)).F-ob Z`.

## CoEndoYoneda Bijection

```agda
record CoEndoYonedaBijection
    {ℓ : Level}
    (C : Category (lsuc ℓ) ℓ)
    (FF : Functor (SET ℓ) C) : Type (lsuc ℓ) where

  private
    module C = Category C
    module FF = Functor FF

  open C
  open FF
  
  -- Inheritance by delegating to `fc`
  field
    fc : FunctionalCategory C FF
  open FunctionalCategory fc

  module CoEndoEquivalenceBijection {EF : Functor C C} {Z : ob} where
    private
      module EF = Functor EF
      module CYEF = Functor (CYEF Z)

    G∘EF : Functor C C
    G∘EF = G ∘F EF

    G∘G∘EF : Functor C C
    G∘G∘EF = G ∘F G∘EF

    CYF∘G : Functor C (SET ℓ)
    CYF∘G = CYF (FF.F-ob T) ∘F G

    CYF∘G∘EF : Functor C (SET ℓ)
    CYF∘G∘EF = CYF∘G ∘F EF  

    private
      module G = Functor G
      module G∘EF = Functor G∘EF
      module G∘G∘EF = Functor G∘G∘EF
      module CYF∘G = Functor CYF∘G
      module CYF∘G∘EF = Functor CYF∘G∘EF

    fft2cyefz : Hom[ FF.F-ob T , CYEF.F-ob Z ]
    fft2cyefz = g id 
    
    -- using
    -- `τz` for `NatTrans (CYEF Z) G∘EF`
    -- and
    -- `fz` for `fst (CYF∘G∘EF.F-ob Z)`
    τz→fz : NatTrans (CYEF Z) G∘EF → fst (CYF∘G∘EF.F-ob Z)
    τz→fz τz = fft2cyefz ⋆ N-ob τz Z

    fz→ay→z2y→fft2gefy :
        fst (CYF∘G∘EF.F-ob Z) 
      → ∀ Y 
      → Hom[ Z , Y ] 
      → Hom[ FF.F-ob T , G∘EF.F-ob Y ]
    fz→ay→z2y→fft2gefy fz Y = λ z2y → fz ⋆ G∘EF.F-hom z2y

    fz→τz-hom : fst (CYF∘G∘EF.F-ob Z) → ∀ Y → Hom[ CYEF.F-ob Y , G∘EF.F-ob  Y ]
    fz→τz-hom fz Y = FF.F-hom (fz→ay→z2y→fft2gefy fz Y) ⋆ N-ob μ (EF.F-ob Y)

    -- again, using
    -- `τz` for `NatTrans (CYEF Z) G∘EF`
    -- and
    -- `fz` for `fst (CYF∘G∘EF.F-ob Z)`
    fz→τz : fst (CYF∘G∘EF.F-ob Z) → NatTrans (CYEF Z) G∘EF
    fz→τz fz = record
      { N-ob = fz→τz-hom fz
      ; N-hom = fz→τz_commute fz
      }

      where       

        fz→τz_commute_lemma : 
          ∀ (fz : fst (CYF∘G∘EF.F-ob Z)) 
            {Y X : ob} 
            (y2x : Hom[ Y , X ]) 
            (z2y : Hom[ Z , Y ])
          →   fz ⋆ G∘EF.F-hom (z2y ⋆ y2x)
            ≡ (fz ⋆ G∘EF.F-hom z2y) ⋆ G∘EF.F-hom y2x
        fz→τz_commute_lemma fz y2x z2y = 
          fz ⋆ G∘EF.F-hom (z2y ⋆ y2x)
            ≡⟨ cong (λ k → fz ⋆ k) (cong G.F-hom (EF.F-seq z2y y2x)) ⟩
          fz ⋆ G.F-hom (EF.F-hom z2y ⋆ EF.F-hom y2x)
            ≡⟨ cong (λ k → fz ⋆ k) (G.F-seq (EF.F-hom z2y) (EF.F-hom y2x)) ⟩
          fz ⋆ G∘EF.F-hom z2y ⋆ G∘EF.F-hom  y2x
            ≡⟨ sym (⋆Assoc fz (G∘EF.F-hom z2y) (G∘EF.F-hom  y2x)) ⟩
          (fz ⋆ G∘EF.F-hom z2y) ⋆ G∘EF.F-hom y2x
            ∎

        fz→ax→z2x→fft2gefx : 
            fst (CYF∘G∘EF.F-ob Z)
          → ∀ X 
          → Hom[ Z , X ] 
          → Hom[ FF.F-ob T , G∘EF.F-ob X ]
        fz→ax→z2x→fft2gefx fz X = λ z2x → fz ⋆ G∘EF.F-hom z2x

        fz→τz_commute : 
          ∀ (fz : fst (CYF∘G∘EF.F-ob Z)) {Y X : ob} (y2x : Hom[ Y , X ])
          →   CYEF.F-hom y2x ⋆ fz→τz-hom fz X 
            ≡ fz→τz-hom fz Y ⋆ G∘EF.F-hom y2x
        fz→τz_commute fz {Y} {X} y2x =
          let
            cyefy2cyefx = CYEF.F-hom y2x
            cyefx2ggefx = FF.F-hom (fz→ax→z2x→fft2gefx fz X)
            cyefy2ggefy = FF.F-hom (fz→ay→z2y→fft2gefy fz Y)
            ggefy2ggefx = FF.F-hom (λ fft2gefy → fft2gefy ⋆ G∘EF.F-hom y2x)
            
          in 
            cyefy2cyefx ⋆ (cyefx2ggefx ⋆ N-ob μ (EF.F-ob X))
              ≡⟨ sym (⋆Assoc cyefy2cyefx cyefx2ggefx (N-ob μ (EF.F-ob X))) ⟩
            (cyefy2cyefx ⋆ cyefx2ggefx) ⋆ N-ob μ (EF.F-ob X)
              ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob X)) 
                  (sym 
                    (FF.F-seq (λ z2y → z2y ⋆ y2x) 
                      (fz→ax→z2x→fft2gefx fz X))) ⟩
              FF.F-hom (λ z2y → fz ⋆ G∘EF.F-hom (z2y ⋆ y2x))
            ⋆ N-ob μ (EF.F-ob X)
              ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob X)) 
                   (cong FF.F-hom (funExt (fz→τz_commute_lemma fz y2x))) ⟩
              FF.F-hom (λ z2y → (fz ⋆ G∘EF.F-hom z2y) ⋆ G∘EF.F-hom  y2x)
            ⋆ N-ob μ (EF.F-ob X)
              ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob X))
                  (FF.F-seq
                    (fz→ay→z2y→fft2gefy fz Y) 
                      (λ fft2gefy → fft2gefy ⋆ G∘EF.F-hom  y2x)) ⟩
            (cyefy2ggefy ⋆ ggefy2ggefx) ⋆ N-ob μ (EF.F-ob X)
              ≡⟨ ⋆Assoc cyefy2ggefy ggefy2ggefx (N-ob μ (EF.F-ob X)) ⟩
            cyefy2ggefy ⋆ (ggefy2ggefx ⋆ N-ob μ (EF.F-ob X))
              ≡⟨ cong (λ k → cyefy2ggefy ⋆ k) (N-hom μ (EF.F-hom y2x)) ⟩
            cyefy2ggefy ⋆ (N-ob μ (EF.F-ob Y) ⋆ G∘EF.F-hom  y2x)
              ≡⟨ sym 
                   (⋆Assoc cyefy2ggefy (N-ob μ (EF.F-ob Y)) (G∘EF.F-hom  y2x)) ⟩
            (cyefy2ggefy ⋆ N-ob μ (EF.F-ob Y)) ⋆ G∘EF.F-hom  y2x
              ∎

    coEndoYonedaBijection : NatTrans (CYEF Z) G∘EF ⇿ fst (CYF∘G∘EF.F-ob Z)
    coEndoYonedaBijection = record
      { to = τz→fz
      ; from = fz→τz
      ; to_from = to_from_proof
      ; from_to = from_to_proof -- uses makeNatTransPath
      }

      where

        to_from_proof : 
          ∀ (fz : fst (CYF∘G∘EF.F-ob Z))
          → τz→fz (fz→τz fz) ≡ fz
        to_from_proof fz = 
          let
            cyefz2ggefz : Hom[ CYEF.F-ob Z , G∘G∘EF.F-ob Z ]
            cyefz2ggefz = FF.F-hom (λ z2z → fz ⋆ G∘EF.F-hom z2z)
          in 
            τz→fz (fz→τz fz)
              ≡⟨ sym (⋆Assoc fft2cyefz cyefz2ggefz (N-ob μ (EF.F-ob Z))) ⟩
            (fft2cyefz ⋆ cyefz2ggefz) ⋆ N-ob μ (EF.F-ob Z)
              ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Z)) 
                  (sym (FF.F-seq (λ _ → id) (λ z2z → fz ⋆ G∘EF.F-hom z2z))) ⟩
            g (fz ⋆ G∘EF.F-hom id) ⋆ N-ob μ (EF.F-ob Z)
              ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Z))
                  (cong FF.F-hom 
                    (funExt (λ _ → to_from_proof_lemma1 fz))) ⟩
            g (fz ⋆ id) ⋆ N-ob μ (EF.F-ob Z)
              ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Z)) 
                  (cong FF.F-hom (funExt (λ _ → ⋆IdR fz))) ⟩
            g fz ⋆ N-ob μ (EF.F-ob Z)
              ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Z)) 
                  (cong FF.F-hom (funExt (λ _ → sym (⋆IdL fz)))) ⟩
            g (id ⋆ fz) ⋆ N-ob μ (EF.F-ob Z)
              ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Z)) 
                  (cong FF.F-hom 
                    (funExt (λ tt* → 
                      cong (λ k → k ⋆ fz) (sym (to_from_proof_lemma2 tt*))))) ⟩
            g (g tt* ⋆ fz) ⋆ N-ob μ (EF.F-ob Z)
              ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Z)) 
                  (FF.F-seq g (λ fft2fft → fft2fft ⋆ fz)) ⟩
            (FF.F-hom g ⋆ G.F-hom fz) ⋆ N-ob μ (EF.F-ob Z)
              ≡⟨ ⋆Assoc (FF.F-hom g) (G.F-hom fz) (N-ob μ (EF.F-ob Z)) ⟩
            FF.F-hom g ⋆ (G.F-hom fz ⋆ N-ob μ (EF.F-ob Z))
              ≡⟨ cong 
                  (λ k → k ⋆ (G.F-hom fz ⋆ N-ob μ (EF.F-ob Z))) (sym η-eq-T) ⟩
            N-ob η (FF.F-ob T) ⋆ (G.F-hom fz ⋆ N-ob μ (EF.F-ob Z))
              ≡⟨ sym 
                  (⋆Assoc (N-ob η (FF.F-ob T))
                    (G.F-hom fz) 
                      (N-ob μ (EF.F-ob Z))) ⟩
            (N-ob η (FF.F-ob T) ⋆ G.F-hom fz) ⋆ N-ob μ (EF.F-ob Z)
              ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Z)) (sym (N-hom η fz)) ⟩
            (fz ⋆ N-ob η (G∘EF.F-ob Z)) ⋆ N-ob μ (EF.F-ob Z)
              ≡⟨ ⋆Assoc fz (N-ob η (G∘EF.F-ob Z)) (N-ob μ (EF.F-ob Z)) ⟩
            fz ⋆ (N-ob η (G∘EF.F-ob Z) ⋆ N-ob μ (EF.F-ob Z))
              ≡⟨ cong (λ k → fz ⋆ k) idˡ ⟩
            fz ⋆ id
              ≡⟨ ⋆IdR fz ⟩
            fz
              ∎
          where   
            to_from_proof_lemma1 : 
              ∀ (fz : fst (CYF∘G∘EF.F-ob Z))
              → fz ⋆ G∘EF.F-hom id ≡ fz ⋆ id
            to_from_proof_lemma1 fz = 
              fz ⋆ G∘EF.F-hom id
                ≡⟨ cong (λ k → fz ⋆ k) G∘EF.F-id ⟩
              fz ⋆ id
                ∎

            to_from_proof_lemma2 : 
              ∀ (tt* : fst T)
              → g tt* ≡ id
            to_from_proof_lemma2 tt* = 
              g tt* 
                ≡⟨ cong FF.F-hom (funExt (λ _ → refl)) ⟩
              FF.F-hom (λ z → z)
                ≡⟨ FF.F-id ⟩
              id
                ∎ 

        from_to_proof' : 
          ∀ (τz : NatTrans (CYEF Z) G∘EF) (Y : ob)
          → fz→τz-hom (τz→fz τz) Y ≡ N-ob τz Y
        from_to_proof' τz Y = 
              FF.F-hom (λ z2y → (fft2cyefz ⋆ (N-ob τz Z)) ⋆ G∘EF.F-hom z2y)
            ⋆ N-ob μ (EF.F-ob Y)
            ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Y)) 
                (cong FF.F-hom 
                  (funExt (λ z2y → 
                    ⋆Assoc fft2cyefz (N-ob τz Z) (G∘EF.F-hom z2y)))) ⟩
            FF.F-hom (λ z2y → fft2cyefz ⋆ ((N-ob τz Z) ⋆ G∘EF.F-hom z2y))
          ⋆ N-ob μ (EF.F-ob Y)
            ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Y))
                (cong FF.F-hom (funExt (λ z2y → 
                    cong (λ k → fft2cyefz ⋆ k) (sym (N-hom τz z2y))))) ⟩
            FF.F-hom (λ z2y → fft2cyefz ⋆ (CYEF.F-hom z2y ⋆ N-ob τz Y)) 
          ⋆ N-ob μ (EF.F-ob Y)
            ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Y)) 
                (cong FF.F-hom 
                  (funExt (λ z2y → 
                    sym (⋆Assoc fft2cyefz (CYEF.F-hom z2y) (N-ob τz Y))))) ⟩
            FF.F-hom (λ z2y → (fft2cyefz ⋆ CYEF.F-hom z2y) ⋆ N-ob τz Y)
          ⋆ N-ob μ (EF.F-ob Y)
            ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Y)) 
                (cong FF.F-hom (funExt (λ z2y → 
                  cong (λ k → k ⋆ N-ob τz Y) 
                    (sym (FF.F-seq (λ _ → id) (λ z2z → z2z ⋆ z2y)))))) ⟩
            FF.F-hom (λ z2y → g (id ⋆ z2y) ⋆ N-ob τz Y)
          ⋆ N-ob μ (EF.F-ob Y)
            ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Y)) 
                (cong FF.F-hom 
                  (funExt (λ z2y → 
                    cong (λ k → FF.F-hom {x = T} k ⋆ N-ob τz Y) 
                      (funExt (λ _ → ⋆IdL z2y))))) ⟩
            FF.F-hom (λ z2y → g (z2y) ⋆ N-ob τz Y)
          ⋆ N-ob μ (EF.F-ob Y)
            ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Y)) 
                (FF.F-seq g (λ fft2cyefy → fft2cyefy ⋆ N-ob τz Y)) ⟩
            (FF.F-hom g ⋆ G.F-hom (N-ob τz Y))
          ⋆ N-ob μ (EF.F-ob Y)
            ≡⟨ ⋆Assoc (FF.F-hom g) (G.F-hom (N-ob τz Y)) (N-ob μ (EF.F-ob Y)) ⟩
              FF.F-hom g
            ⋆ (G.F-hom (N-ob τz Y)⋆ N-ob μ (EF.F-ob Y))
            ≡⟨ cong (λ k → k ⋆ (G.F-hom (N-ob τz Y) ⋆ N-ob μ (EF.F-ob Y))) 
                (sym η-eq) ⟩
            N-ob η (CYEF.F-ob Y)
          ⋆ (G.F-hom (N-ob τz Y) ⋆ N-ob μ (EF.F-ob Y))
            ≡⟨ sym (⋆Assoc (N-ob η (CYEF.F-ob Y)) 
                (G.F-hom (N-ob τz Y)) (N-ob μ (EF.F-ob Y))) ⟩
            (N-ob η (CYEF.F-ob Y) ⋆ G.F-hom (N-ob τz Y))
          ⋆ N-ob μ (EF.F-ob Y)
            ≡⟨ cong (λ k → k ⋆ N-ob μ (EF.F-ob Y)) (sym (N-hom η (N-ob τz Y))) ⟩
            (N-ob τz Y ⋆ N-ob η (G∘EF.F-ob  Y))
          ⋆ N-ob μ (EF.F-ob Y)
            ≡⟨ ⋆Assoc (N-ob τz Y) (N-ob η (G∘EF.F-ob  Y)) (N-ob μ (EF.F-ob Y)) ⟩
            N-ob τz Y
          ⋆ (N-ob η (G∘EF.F-ob  Y) ⋆ N-ob μ (EF.F-ob Y))
            ≡⟨ cong (λ k → N-ob τz Y ⋆ k) idˡ ⟩
          N-ob τz Y ⋆ id
            ≡⟨ ⋆IdR (N-ob τz Y) ⟩
          N-ob τz Y
            ∎

        from_to_proof : 
          ∀ (τz : NatTrans (CYEF Z) G∘EF) 
          → fz→τz (τz→fz τz) ≡ τz
        from_to_proof τz = makeNatTransPath (funExt (from_to_proof' τz))
```

## Purity

We define `hSetMonad`, the standard in functional programming formulation. From its members `M`,
`mPure` and `mApply`, and their laws `mApply-pure`, `mPure-mApply` and `mApply-assoc`, we define
`mMap`, `mPure` and `mJoin` and their laws `mMap-id`, `mMap-comp`, `mJoin-mPure`, `mJoin-mMap-mPure`
and `mJoin-mMap-mJoin`, as well as the naturality of `mPure` and `mJoin` of the corresponding
standard categorical formulation. Moreover we also define how to recover `mApply` from `mJoin` and
`mMap`.

```agda
record hSetMonad {ℓ : Level} : Type (lsuc ℓ) where
  field
    M : hSet ℓ → hSet ℓ
    mPure : ∀ {Z : hSet ℓ} → fst Z → fst (M Z)
    mApply : ∀ {Z Y : hSet ℓ} → (fst Z → fst (M Y)) → fst (M Z) → fst (M Y)
    
    mApply-pure : 
      ∀ {Z Y : hSet ℓ} {z→my : fst Z → fst (M Y)} {z : fst Z}
      →   mApply z→my (mPure {Z} z) 
        ≡ z→my z

    mPure-mApply : 
      ∀ {Z : hSet ℓ} {mz : fst (M Z)}
      →   mApply mPure mz 
        ≡ mz

    mApply-assoc : 
      ∀ {Z Y X : hSet ℓ} 
        {z→my : fst Z → fst (M Y)} 
        {y→mx : fst Y → fst (M X)} 
        {mz : fst (M Z)}
      →   mApply y→mx (mApply z→my mz)
        ≡ mApply (λ z → mApply y→mx (z→my z)) mz
    
  mMap : ∀ {Z Y : hSet ℓ} → (fst Z → fst Y) → fst (M Z) → fst (M Y)
  mMap {Z} {Y} z→my = mApply (λ z → mPure (z→my z))

  mMap-id : ∀ {Z : hSet ℓ} (mz : fst (M Z)) → mMap (λ z → z) mz ≡ mz
  mMap-id {Z} mz = mPure-mApply -- {Z} {mz}

  mMap-comp : 
    ∀ {Z Y X : hSet ℓ} (f : fst Z → fst Y) (g : fst Y → fst X) (mz : fst (M Z))
    → mMap (λ z → g (f z)) mz ≡ mMap g (mMap f mz)
  mMap-comp {Z} {Y} {X} f g mz =
    sym (
      mMap g (mMap f mz)
        ≡⟨ mApply-assoc ⟩
      mApply (λ z → mApply (λ y → mPure (g y)) (mPure (f z))) mz
        ≡⟨ cong (λ k → mApply k mz) (funExt (λ z → mApply-pure {Y} {X})) ⟩
      mMap (λ z → g (f z)) mz ∎
    )

  mJoin : ∀ {Z : hSet ℓ} → fst (M (M Z)) → fst (M Z)
  mJoin = mApply (λ mz → mz)

  mJoin-mPure : 
    ∀ {Z : hSet ℓ} (mz : fst (M Z)) 
    → mJoin (mPure mz) ≡ mz
  mJoin-mPure {Z} mz = mApply-pure

  mJoin-mMap-mPure : 
    ∀ {Z : hSet ℓ} (mz : fst (M Z)) 
    → mJoin (mMap mPure mz) ≡ mz
  mJoin-mMap-mPure {Z} mz = 
    mJoin (mMap mPure mz)
      ≡⟨ mApply-assoc ⟩
    mApply (λ z → mApply (λ mz' → mz') (mPure (mPure z))) mz
      ≡⟨ cong (λ k → mApply k mz) 
           (funExt (λ z → mApply-pure {M Z} {Z} {λ mz' → mz'} {mPure z})) ⟩
    mApply mPure mz
      ≡⟨ mPure-mApply ⟩
    mz ∎

  mJoin-mMap-mJoin : 
    ∀ {Z : hSet ℓ} (mmmz : fst (M (M (M Z)))) 
    → mJoin (mMap mJoin mmmz) ≡ mJoin (mJoin mmmz)
  mJoin-mMap-mJoin {Z} mmmz =
    mJoin (mMap mJoin mmmz)
      ≡⟨ mApply-assoc ⟩
    mApply (λ mmz → mApply (λ mz → mz) (mPure (mJoin mmz))) mmmz
      ≡⟨ cong (λ k → mApply k mmmz) (funExt (λ mmz → mApply-pure {M Z} {Z} {λ mz → mz} {mJoin mmz})) ⟩
    mApply mJoin mmmz
      ≡⟨ sym (mApply-assoc {M (M Z)}) ⟩
    mJoin (mJoin mmmz) ∎

  mPure-natural : 
    ∀ {Z Y : hSet ℓ} (z→y : fst Z → fst Y) (z : fst Z)
    → mMap z→y (mPure z) ≡ mPure (z→y z)
  mPure-natural {Z} {Y} z→y z = mApply-pure {Z} {Y} {λ z' → mPure (z→y z')} {z}

  mJoin-natural : 
    ∀ {Z Y : hSet ℓ} (z→y : fst Z → fst Y) (mmz : fst (M (M Z)))
    → mMap z→y (mJoin mmz) ≡ mJoin (mMap (mMap z→y) mmz)
  mJoin-natural {Z} {Y} z→y mmz =
    mMap z→y (mJoin mmz)
      ≡⟨ mApply-assoc ⟩
    mApply (λ mz → mMap z→y mz) mmz
      ≡⟨ cong (λ k → mApply k mmz) 
           (funExt (λ mz → sym 
             (mApply-pure {M Y} {Y} {λ mz' → mz'} {mMap z→y mz}))) ⟩
    mApply (λ mz → mApply (λ mz' → mz') (mPure (mMap z→y mz))) mmz
      ≡⟨ sym (mApply-assoc) ⟩
    mJoin (mMap (mMap z→y) mmz) ∎

  mApply-from-join : 
    ∀ {Z Y : hSet ℓ} (z→my : fst Z → fst (M Y)) (mz : fst (M Z))
    → mJoin (mMap z→my mz) ≡ mApply z→my mz
  mApply-from-join {Z} {Y} z→my mz =
    mJoin (mMap z→my mz)
      ≡⟨ mApply-assoc ⟩
    mApply (λ z → mApply (λ mz' → mz') (mPure (z→my z))) mz
      ≡⟨ cong (λ k → mApply k mz) 
           (funExt (λ z → mApply-pure {M Y} {Y} {λ mz' → mz'} {z→my z})) ⟩
    mApply z→my mz ∎
```

We formulate the purity theorems inside a parameterized module over a given `hSetMonad`.

```agda
open import Function.Base using (id; _∘_)

module PurityTheorems {ℓ : Level} (hSM : hSetMonad {ℓ}) where
  open hSetMonad hSM

  Property = Type (lsuc ℓ)

  record _⇔_ (p q : Property) : Property where
    field
      to : p → q
      from : q → p
```

We define `Idempotent`, one of the many pointful characterizations of purity of `nLab`.

```agda
  record Idempotent : Property where
    field
      idempotent : 
        ∀ {Z : hSet ℓ} 
          (mz : fst (M Z)) 
        →   mMap mPure mz 
          ≡ mPure {M Z} mz

  open Idempotent
```

We also define `EnforcingPurity` which is, trivially, equivalent with `Idempotent`.

```agda
  record EnforcingPurity : Property where
    field
      enforcingPurity : 
        ∀ {Z : hSet ℓ} 
          (mz : fst (M Z))
        →   mApply (mPure ∘ mPure) mz 
          ≡ mPure {M Z} mz

  open EnforcingPurity

  idempotent-equiv-enforcing-purity : Idempotent ⇔ EnforcingPurity 
  idempotent-equiv-enforcing-purity = record 
    { to = 
        λ i → record
          { enforcingPurity = λ mz →
              mApply (mPure ∘ mPure) mz
                ≡⟨ refl ⟩
              mMap mPure mz
                ≡⟨ idempotent i mz ⟩
              mPure mz
            ∎
          }
    ; from = 
        λ ep → record
          { idempotent = λ mz →
              mMap mPure mz
                ≡⟨ refl ⟩
              mApply (mPure ∘ mPure) mz
                ≡⟨ enforcingPurity ep mz ⟩
              mPure mz
            ∎
          }
    }
```

We now prove that a `Kleisli` category being a `KleisliBasicFunctionalCategory` category is
equivalent to its monad being an `Idempotent` monad.

```agda
  Kleisli : Category (lsuc ℓ) ℓ
  Kleisli = record
    { ob = hSet ℓ
    ; Hom[_,_] = λ Z Y → fst Z → fst (M Y)
    ; id = λ {Z} → mPure {Z}
    ; _⋆_ = λ {Z Y X} z→my y→mx z → mApply y→mx (z→my z)
    ; ⋆IdL = λ {Z Y} z→my → funExt (λ z → mApply-pure {Z} {Y} {z→my} {z})
    ; ⋆IdR = λ {Z Y} _ → funExt (λ z → mPure-mApply)
    ; ⋆Assoc = λ {Z Y X W} _ _ _ → funExt (λ _ → mApply-assoc)
    ; isSetHom = λ {Z Y} → isSetΠ (λ _ → snd (M Y))
    }

  KFF : Functor (SET ℓ) Kleisli
  KFF = record
    { F-ob = λ Z → Z
    ; F-hom = λ z2y → (λ z → mPure (z2y z))
    ; F-id = refl
    ; F-seq = λ _ _ → funExt (λ _ → sym mApply-pure)
    }

  KleisliBasicFunctionalCategory : Type (lsuc ℓ)
  KleisliBasicFunctionalCategory = 
    BasicFunctionalCategory Kleisli KFF

  idempotent-equiv-kleisli-basic-functional-category : 
    KleisliBasicFunctionalCategory ⇔ Idempotent
  idempotent-equiv-kleisli-basic-functional-category = record
    { to = λ kfc → record 
        { idempotent = λ {Z} mz → 
            let
              open BasicFunctionalCategory kfc

              eval_lemma : 
                ∀ {Z : hSet ℓ} (mz : fst (M Z))
                →   mApply (N-ob η Z) mz
                  ≡ mPure (λ _ → mz)
              eval_lemma {Z} mz = 
                let
                  t→mz = λ _ → mz
                  
                  left-eq : 
                      mApply (F-hom G t→mz) (N-ob η T tt*) 
                    ≡ mPure t→mz
                  left-eq = 
                    mApply (F-hom G t→mz) (N-ob η T tt*)
                      ≡⟨ cong (λ k → mApply (F-hom G t→mz) (k tt*)) η-eq-T ⟩
                    mApply (F-hom G t→mz) (mPure (λ _ → mPure tt*))
                      ≡⟨ mApply-pure ⟩
                    F-hom G t→mz (λ _ → mPure tt*)
                      ≡⟨ refl ⟩
                    mPure (λ _ → mApply t→mz (mPure tt*))
                      ≡⟨ cong (λ k → mPure (λ (_ : fst T) → k)) mApply-pure ⟩
                    mPure {F-ob G Z} (λ _ → t→mz tt*)
                      ≡⟨ refl ⟩
                    mPure {F-ob G Z} t→mz
                      ∎
                in  
                  cong (λ t→mgz → t→mgz tt*) (N-hom η t→mz) ∙ left-eq
              
              eval : fst (M (F-ob G Z)) → fst (M (M Z))
              eval = mApply (λ t→mz → mPure (t→mz tt*))

              idempotent_lemma : 
                  (z : fst Z) 
                →   eval (N-ob η Z z) 
                  ≡ mPure (mPure z)
              idempotent_lemma z = 
                eval (N-ob η Z z)
                  ≡⟨ sym (cong eval mApply-pure) ⟩
                eval (mApply (N-ob η Z) (mPure z))
                  ≡⟨ cong eval (eval_lemma (mPure z)) ⟩
                eval (mPure (λ _ → mPure z))
                  ≡⟨ mApply-pure ⟩
                mPure (mPure z)
                  ∎

            in 
              mMap mPure mz
                ≡⟨ refl ⟩
              mApply (λ z → mPure (mPure z)) mz
                ≡⟨ sym (cong (λ k → mApply k mz) (funExt idempotent_lemma)) ⟩
              mApply (λ z → eval (N-ob η Z z)) mz
                ≡⟨ sym mApply-assoc ⟩
              eval (mApply (N-ob η Z) mz)
                ≡⟨ cong eval (eval_lemma mz) ⟩
              eval (mPure (λ _ → mz))
                ≡⟨ mApply-pure ⟩
              mPure mz
                ∎
        }
    ; from = λ i → 
        let
          T : hSet ℓ
          T = (Unit* , isSetUnit*)

          GM : (Z : hSet ℓ) → hSet ℓ
          GM Z = ((fst T → fst (M Z)) , isSetΠ (λ _ → snd (M Z)))

          mApply_lemma :
            ∀ {Z : hSet ℓ} (
              mz : fst (M Z))
            →   mApply (λ z → mPure (λ _ → mPure z)) mz 
              ≡ mPure (λ _ → mz)
          mApply_lemma {Z} mz = 
            let 
              MZ = M Z
              GMZ = GM Z
              MGMZ = M GMZ
              gmz = λ (_ : fst T) → mz
              mz→mgmz = λ (mz : fst MZ) → mPure (λ _ → mz)
            in 
              mApply (λ z → mPure (λ _ → mPure z)) mz
                ≡⟨ sym (cong (λ k → mApply k mz) (funExt (λ z → mApply-pure))) ⟩
              mApply (λ z → mApply mz→mgmz (mPure (mPure z))) mz
                ≡⟨ sym mApply-assoc ⟩
              mApply mz→mgmz (mApply (λ z → mPure (mPure z)) mz)
                ≡⟨ cong (λ k → mApply mz→mgmz k) refl ⟩
              mApply mz→mgmz (mMap mPure mz)
                ≡⟨ cong (λ k → mApply mz→mgmz k) (idempotent i mz) ⟩
              mApply mz→mgmz (mPure mz)
                ≡⟨ mApply-pure ⟩
              mPure (λ _ → mz)
                ∎
          comm :
            ∀ {Y X : hSet ℓ} 
              (y→mx : fst Y → fst (M X))
              (y : fst Y)
            →   mApply (λ x → mPure (λ _ → mPure x)) (y→mx y)
              ≡ mApply 
                  (λ gmy → mPure (λ t → mApply y→mx (gmy t))) 
                    (mPure (λ _ → mPure y))
          comm {Y} {X} y→mx y = 
            let 
              gmy→mgmx : fst (GM Y) → fst (M (GM X))
              gmy→mgmx gmy = mPure (λ t → mApply y→mx (gmy t)) 
            in 
              mApply (λ x → mPure (λ _ → mPure x)) (y→mx y)
                ≡⟨ mApply_lemma (y→mx y) ⟩
              mPure (λ _ → y→mx y)
                ≡⟨ sym (cong (λ k → mPure (λ _ → k)) mApply-pure) ⟩
              mPure (λ _ → mApply y→mx (mPure y))
                ≡⟨ sym mApply-pure ⟩
              mApply gmy→mgmx (mPure (λ _ → mPure y))
                ∎
        in
          record 
            { η = record 
                  { N-ob = λ Y y → mPure (λ _ → mPure y)
                  ; N-hom = λ {Y X} y→mx → funExt (comm y→mx)
                  }
            ; η-eq-T = refl
            }
    }
```

We now define `MonadicTerminalTypeSubSingleton`

```agda
  T : hSet ℓ
  T = (Unit* , isSetUnit*)

  record MonadicTerminalTypeSubSingleton : Property where
    field
      monadic-terminal-type-sub-singleton : 
        ∀ (mt : fst (M T)) 
        →   mt
          ≡ mPure tt*

  open MonadicTerminalTypeSubSingleton
```

Now we prove `enforcing-purity-implies-monadic-terminal-type-subsingleton`.

The `proof` below is a proof of exceptional beauty!

Starting with an arbitrary monadic computation `mt` of type `fst (M T)`: equational reasoning forces
it to collapse to a single canonical value: `mPure tt*`.

I am not sure who proved it originally.

F. William Lawvere and Ernest Manes have certainly contributed to setting the seene, but I think
that it was Francis Borceux who first presented the equational proof formalized below in his book.

```agda
  enforcing-purity-implies-monadic-terminal-type-subsingleton : 
      EnforcingPurity → MonadicTerminalTypeSubSingleton
  enforcing-purity-implies-monadic-terminal-type-subsingleton ep = record
    { monadic-terminal-type-sub-singleton = proof }
    where
      MT = M T
      MMT = M MT

      mmt→mt : fst MMT → fst MT
      mmt→mt = mApply (λ (_ : fst MT) → mPure tt*)

      proof : 
        ∀ (mt : fst (M T)) 
        →   mt 
          ≡ mPure tt*
      proof mt =
        mt
          ≡⟨ sym mPure-mApply ⟩
        mApply mPure mt
          ≡⟨ cong (λ k → mApply {T} {T} (λ t → mPure (k t)) mt) (funExt (λ t → refl)) ⟩
        mApply (λ _ → mPure tt*) mt
          ≡⟨ cong (λ k → mApply k mt) (funExt (λ _ → sym mApply-pure)) ⟩
        mApply (λ t → mmt→mt ((mPure ∘ mPure) t)) mt
          ≡⟨ sym mApply-assoc ⟩
        mmt→mt (mApply (mPure ∘ mPure) mt)
          ≡⟨ cong mmt→mt (enforcingPurity ep mt) ⟩
        mmt→mt (mPure mt)
          ≡⟨ mApply-pure ⟩
        mPure tt*
          ∎
```

## Examples

Here are some concrete examples.

They use `examplesMonad` in order to disambiguate from `hSetMonad`.

We could have used `hSetMonad` but then thinks would become more complex.

For the pupose of the examples below, `examplesMonad` is an appropriate  pragmatic choice.

```agda

open import Data.Maybe hiding (_>>=_)
open import Data.List
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary
open import Cubical.Data.Empty

private
  variable
    ℓ : Level

record examplesMonad {ℓ : Level} (M : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field
    pure : ∀ {Z : Type ℓ} → Z → M Z
    _>>=_ : ∀ {Z Y : Type ℓ} → M Z → (Z → M Y) → M Y

open examplesMonad {{...}}

EnforcingPurityEq : 
  ∀ {ℓ} (M : Type ℓ → Type ℓ) ⦃ _ : examplesMonad M ⦄ → Type (lsuc ℓ)
EnforcingPurityEq {ℓ} M = 
  ∀ {Z : Type ℓ} (mz : M Z) 
  →   mz >>= (pure ∘ pure)
    ≡ pure mz

instance
  MaybeMonad : ∀ {ℓ} → examplesMonad {ℓ} Maybe
  MaybeMonad = record
    { pure = just
    ; _>>=_ = λ { nothing _ → nothing ; (just z) z→my → z→my z }
    }

maybe-not-pure : 
  ∀ {ℓ}
  → ¬ EnforcingPurityEq {ℓ} Maybe
maybe-not-pure {ℓ} h =
  let T = Lift ℓ Unit
  in contradiction-from (h nothing)
  where
    T = Lift ℓ Unit
    contradiction-from : 
        nothing 
      ≡ just nothing → ⊥
    contradiction-from p = transport (λ i → P (p i)) tt*
      where
        P : Maybe (Maybe T) → Type lzero
        P nothing = Unit*
        P (just _) = ⊥

instance
  ListMonad : ∀ {ℓ} → examplesMonad {ℓ} List
  ListMonad = record
    { pure = λ z → z ∷ []
    ; _>>=_ = λ zs z→my → concatMap z→my zs
    }

list-not-pure : ∀ {ℓ} → ¬ EnforcingPurityEq {ℓ} List
list-not-pure {ℓ} h =
  let T = Lift ℓ Unit
  in contradiction-from (h (tt* ∷ tt* ∷ []))
  where
    T = Lift ℓ Unit
    contradiction-from : 
      (tt* ∷ []) ∷ (tt* ∷ []) ∷ []  ≡ (tt* ∷ tt* ∷ []) ∷ [] → ⊥
    contradiction-from p = transport (λ i → P (p i)) tt*
      where
        P : List (List T) → Type lzero
        P (_ ∷ _ ∷ _) = Unit*
        P _ = ⊥

Read : ∀ {ℓ} → Type ℓ → Type ℓ → Type ℓ
Read R Z = R → Z

instance
  ReadMonad : ∀ {ℓ} {R : Type ℓ} → examplesMonad (Read R)
  ReadMonad = record
    { pure = λ z _ → z
    ; _>>=_ = λ m z→ry r → z→ry (m r) r
    }

SubSingleton : ∀ {ℓ} → Type ℓ → Type ℓ
SubSingleton A = (z y : A) → z ≡ y

read-purity-implies : 
  ∀ {ℓ} (R : Type ℓ) 
  → EnforcingPurityEq (Read R) → SubSingleton R
read-purity-implies R h r1 r2 =
  cong (λ _op_ → r1 op r2) (h id)

Write : ∀ {ℓ} → Type ℓ → Type ℓ → Type ℓ
Write W Z = Z × W

module WriteMonadModule {ℓ : Level} (W : Type ℓ) (e : W) (_∙_ : W → W → W) where

  Trivial : Type ℓ
  Trivial = ∀ w → w ≡ e
  
  instance
    WriteMonad : examplesMonad (Write W)
    WriteMonad = record
      { pure = λ z → (z , e)
      ; _>>=_ = λ mz z→wy → let (y , w) = z→wy (fst mz) in (y , snd mz ∙ w)
      }

  write-purity-implies : EnforcingPurityEq (Write W) → Trivial
  write-purity-implies h w =
    sym (cong snd (cong fst (h (e , w))))

State : ∀ {ℓ} → Type ℓ → Type ℓ → Type ℓ
State S Z = S → Z × S

instance
  StateMonad : ∀ {ℓ} {S : Type ℓ} → examplesMonad (State S)
  StateMonad = record
    { pure = λ z s → (z , s)
    ; _>>=_ = λ mz z→sy s → let (z , s') = mz s in z→sy z s'
    }

state-purity-implies : 
  ∀ {ℓ} (S : Type ℓ)
  → EnforcingPurityEq (State S) → SubSingleton S
state-purity-implies S h s1 s2 =
  cong (λ m → fst (m s2)) (cong (λ mm → fst (mm s1)) (h (λ s → (s , s))))

Cont : ∀ {ℓ} → Type ℓ → Type ℓ → Type ℓ
Cont R Z = (Z → R) → R

instance
  ContMonad : ∀ {ℓ} {R : Type ℓ} → examplesMonad (Cont R)
  ContMonad = record
    { pure = λ z k → k z
    ; _>>=_ = λ mz z→my k → mz (λ z → z→my z k)
    }

cont-purity-implies : 
  ∀ {ℓ} (R : Type ℓ) 
  → EnforcingPurityEq (Cont R) → SubSingleton R
cont-purity-implies R h r1 r2 =
  let m1 : Cont R R
      m1 = λ _ → r1
  in cong (λ mm → mm (λ _ → r2)) (h m1)

-- `IO` simulated as `ErrorState`
ErrorState : ∀ {ℓ} → Type ℓ → Type ℓ → Type ℓ → Type ℓ
ErrorState E S Z = S → (E × S) ⊎ (Z × S)

instance
  ErrorStateMonad : 
    ∀ {ℓ} {E S : Type ℓ} 
    → examplesMonad (ErrorState E S)
  ErrorStateMonad {ℓ} {E} {S} = record
    { pure = λ z s → inr (z , s)
    ; _>>=_ = bind
    }
    where
      bind : 
        ∀ {Z Y : Type ℓ} 
        → ErrorState E S Z 
        → (Z → ErrorState E S Y) 
        → ErrorState E S Y
      bind mz z→my s = helper (mz s) z→my
        where
          helper : 
            ∀ {Z Y}
            → (E × S) ⊎ (Z × S)
            → (Z → ErrorState E S Y) 
            → (E × S) ⊎ (Y × S)
          helper (inl err) _ = inl err
          helper (inr (z , s')) z→my = z→my z s'

io-not-pure : 
  ∀ {ℓ} {E S : Type ℓ} (e : E) (s : S) 
  → ¬ EnforcingPurityEq (ErrorState E S)
io-not-pure {ℓ} {E} {S} e s h =
  let m = λ s → inl (e , s)
  in contradiction-from (cong (λ mm → mm s) (h m))
  where
    contradiction-from : 
      {m : ErrorState E S (Lift ℓ Unit)}
      → inl (e , s) ≡ inr (m , s) → ⊥
    contradiction-from p = transport (λ i → P (p i)) tt*
      where
        P : (E × S) ⊎ (ErrorState E S (Lift ℓ Unit) × S) → Type lzero
        P (inl _) = Unit*
        P (inr _) = ⊥
```

## Purity, Subsingletons, and the Role of CoEndoYoneda

The theorem `enforcing-purity-implies-monadic-terminal-type-subsingleton` offers a remarkable
diagnostic insight into categorical functional programming.

The subsingleton condition eliminates many classic impure computational effects:

- `Maybe`: has $2$ elements on the terminal type 
  (`nothing` and `just tt*`) $\implies$ not pure!

- `List`: has infinitely many elements on the terminal type 
  (`[]`, `[tt*]`, `[tt*, tt*]`, $\dots$) $\implies$ not pure!

- `State`: has $|S|^{|S|}$ state transformations on $\mathbf{1}$
  $\implies$ not pure!

- `IO` / `ErrorState`: has error and effect branches 
  $\implies$ not pure!

### The Subtlety of `Reader`

Yet this diagnostic test reveals a profound mathematical subtlety:
$$\text{Reader } R\ \mathbf{1} = (R \to \mathbf{1}) \cong \mathbf{1}$$

`Reader` passes the $M(\mathbf{1}) \cong \mathbf{1}$ test! 

It is, afaik, the only classic effect that survives this filter, because querying an environment
does not alter the uniqueness of computing a terminal result.

This is precisely where the `BasicFunctionalCategory` law `η-eq-T` proves essential: it provides
the pointfree structural characterization of purity capable of distinguishing truly pure computation
from environment and context passing which is also not truly pure computation although it survives
the filter above.

Thanks for listening.
