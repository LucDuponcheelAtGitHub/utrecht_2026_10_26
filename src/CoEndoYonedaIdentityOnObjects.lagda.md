# CoEndoYoneda with `FF` Identity on Objects

In this file, we explore the CoEndoYoneda theorem under the sole restriction that the functor `FF`
is the **identity on objects**.

We do not restrict the morphisms (homomorphisms) in any way: they can be effectful computations,
Kleisli arrows, partial maps, relations, or abstract morphisms. We only require:
1. The objects of category $C$ are sets: $\mathrm{ob } C = \mathrm{hSet } \ell$.
2. The functor $FF : \mathbf{SET } \ell \to C$ has $FF.F\text{-ob } Z = Z$.

This restriction simplifies the categorical landscape:
- Every object $Y \in C$ is literally a set, so $FF.F\text{-ob } Y = Y$ definitionally.
- The terminal set $T = \mathbf{1}$ satisfies $FF.F\text{-ob } T = T$ definitionally.
- The point generator $g : \mathrm{fst } Y \to \mathrm{Hom}[ T , Y ]$ is a set-theoretic function
  between sets, so $FF.F\text{-hom } g$ immediately constructs $\eta_Y : \mathrm{Hom}[ Y , G(Y) ]$
  for **every object** $Y$ in the category!
- The law `η-eq-T` holds directly, and coincides with the CoEndoYoneda `universal-element`.

```agda
{-# OPTIONS --cubical --guardedness #-}

module CoEndoYonedaIdentityOnObjects where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets

open Functor
open NatTrans

-- Standard bijection record as in CoEndoYoneda.lagda.md
record _⇿_ {ℓ ℓ' : Level} (Z : Type ℓ) (Y : Type ℓ') : Type (ℓ ⊔ ℓ') where
  field
    to : Z → Y
    from : Y → Z
    to_from : ∀ z → to (from z) ≡ z
    from_to : ∀ y → from (to y) ≡ y
```

## 1. Object-Constrained Functors

An `ObjectConstrainedFunctor` is a functor whose object mapping is specified upfront
as a parameter rather than an unconstrained field.

```agda
record ObjectConstrainedFunctor 
    {ℓC ℓC' ℓD ℓD' : Level}
    (C : Category ℓC ℓC') 
    (D : Category ℓD ℓD')
    (ob-map : Category.ob C → Category.ob D) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  open Category

  field
    F-hom : {x y : ob C} → C [ x , y ] → D [ ob-map x , ob-map y ]
    F-id  : {x : ob C} → F-hom (C .id) ≡ D .id {x = ob-map x}
    F-seq : {x y z : ob C} (f : C [ x , y ]) (g : C [ y , z ])
          → F-hom (f ⋆⟨ C ⟩ g) ≡ F-hom f ⋆⟨ D ⟩ F-hom g

  asFunctor : Functor C D
  asFunctor = record
    { F-ob = ob-map
    ; F-hom = F-hom
    ; F-id = F-id
    ; F-seq = F-seq
    }
```

## 2. Categories with `hSet ℓ` Objects

We consider any category whose objects are `hSet ℓ`. The morphisms `Hom[ Z , Y ]` remain
completely general and abstract.

```agda
record HSetCategory (ℓ : Level) : Type (lsuc ℓ) where
  field
    Hom : hSet ℓ → hSet ℓ → Type ℓ
    isSetHom : ∀ {Z Y} → isSet (Hom Z Y)
    id : ∀ {Z} → Hom Z Z
    _⋆_ : ∀ {Z Y X} → Hom Z Y → Hom Y X → Hom Z X
    ⋆IdL : ∀ {Z Y} (f : Hom Z Y) → id ⋆ f ≡ f
    ⋆IdR : ∀ {Z Y} (f : Hom Z Y) → f ⋆ id ≡ f
    ⋆Assoc : ∀ {Z Y X W} (f : Hom Z Y) (g : Hom Y X) (h : Hom X W) → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)

  asCategory : Category (lsuc ℓ) ℓ
  Category.ob asCategory = hSet ℓ
  Category.Hom[_,_] asCategory = Hom
  Category.isSetHom asCategory = isSetHom
  Category.id asCategory = id
  Category._⋆_ asCategory = _⋆_
  Category.⋆IdL asCategory = ⋆IdL
  Category.⋆IdR asCategory = ⋆IdR
  Category.⋆Assoc asCategory = ⋆Assoc
```

## 3. Pre-Functional Category with `FF` Identity on Objects

Here `FF` is an `ObjectConstrainedFunctor` whose object action is the identity `λ Z → Z`.
Notice: **We do not assume $\eta$ or $\mu$.**

```agda
module PreFunctionalIO {ℓ : Level} 
    (hsc : HSetCategory ℓ) 
    (ocf : ObjectConstrainedFunctor (SET ℓ) (HSetCategory.asCategory hsc) (λ Z → Z)) where

  open HSetCategory hsc
  open ObjectConstrainedFunctor ocf

  C : Category (lsuc ℓ) ℓ
  C = asCategory

  FF : Functor (SET ℓ) C
  FF = asFunctor

  -- T is the terminal object in SET ℓ
  T : hSet ℓ
  T = (Unit* , isSetUnit*)

  -- tt* : fst T
  -- tt* = tt*

  -- CoYoneda functor
  CYF : hSet ℓ → Functor C (SET ℓ)
  CYF Z = record
    { F-ob = λ Y → (Hom Z Y , isSetHom)
    ; F-hom = λ y2x → (λ z2y → z2y ⋆ y2x)
    ; F-id = funExt ⋆IdR
    ; F-seq = λ y2x x2w → funExt (λ z2y → sym (⋆Assoc z2y y2x x2w))
    }

  -- CoEndo functor: FF ∘F (CYF Z)
  -- Because FF is the identity on objects, (CYEF Z).F-ob Y = (Hom Z Y , isSetHom) definitionally!
  CYEF : hSet ℓ → Functor C C
  CYEF Z = FF ∘F (CYF Z)

  -- G = CYEF T
  G : Functor C C
  G = CYEF T

  private
    module G = Functor G

  -- Global element generator:
  -- Takes an element z : fst Z and returns a morphism from T to Z.
  g : {Z : hSet ℓ} → fst Z → Hom T Z
  g z = F-hom (λ _ → z)
```

## 4. Canonical Construction of $\eta$ and `η-eq-T`

Because every object $Y$ is a set, the point generator $g$ gives a set-level function:
$$g : \mathrm{fst } Y \longrightarrow \mathrm{Hom } T Y = \mathrm{fst } (G .F\text{-ob } Y)$$

Applying `F-hom` (the action of `FF` on morphisms) immediately constructs a morphism in $C$:
$$\eta_Y := F\text{-hom } g \in \mathrm{Hom } Y (G(Y))$$
**for every object $Y$ in the category!**

```agda
  -- Component of η for any object Y:
  η-hom : (Y : hSet ℓ) → Hom Y (G.F-ob Y)
  η-hom Y = F-hom g

  -- For Y = T, η-hom T satisfies η-eq-T:
  η-eq-T-proof : η-hom T ≡ g (g tt*)
  η-eq-T-proof = 
    F-hom g
      ≡⟨ cong F-hom (funExt (λ (t : Unit*) → refl)) ⟩
    F-hom (λ _ → g tt*)
      ∎
```

## 5. The CoEndoYoneda Bijection and Universal Element

Now we show that the CoEndoYoneda bijection maps $\mathrm{id}_G$ directly to this $\eta_T$:

```agda
  module CoEndoEquivalenceIO {EF : Functor C C} {Z : hSet ℓ} where
    private
      module EF = Functor EF
      module CYEF = Functor (CYEF Z)

    G∘EF : Functor C C
    G∘EF = G ∘F EF

    CYF∘G∘EF : Functor C (SET ℓ)
    CYF∘G∘EF = (CYF T ∘F G) ∘F EF

    fft2cyefz : Hom T (CYEF.F-ob Z)
    fft2cyefz = g id

    τz→fz : NatTrans (CYEF Z) G∘EF → fst (CYF∘G∘EF.F-ob Z)
    τz→fz τz = fft2cyefz ⋆ N-ob τz Z

  module UniversalOriginIO where
    open CoEndoEquivalenceIO {EF = Id} {Z = T}

    idG : NatTrans (CYEF T) G∘EF
    idG = record
      { N-ob = λ _ → id
      ; N-hom = λ f → 
          G.F-hom f ⋆ id
            ≡⟨ ⋆IdR (G.F-hom f) ⟩
          G.F-hom f
            ≡⟨ sym (⋆IdL (G.F-hom f)) ⟩
          id ⋆ G.F-hom f
            ∎
      }

    universal-element : fst (CYF∘G∘EF.F-ob T)
    universal-element = τz→fz idG

    universal-element-is-g-id : universal-element ≡ g id
    universal-element-is-g-id = ⋆IdR fft2cyefz

    g-tt*-is-id : ∀ (t : fst T) → g t ≡ id
    g-tt*-is-id t = 
      F-hom (λ _ → t)
        ≡⟨ cong F-hom (funExt (λ z → z)) ⟩
      F-hom (λ z → z)
        ≡⟨ F-id ⟩
      id
        ∎

    universal-element-is-g-g-tt* : universal-element ≡ g (g tt*)
    universal-element-is-g-g-tt* = 
      universal-element
        ≡⟨ universal-element-is-g-id ⟩
      g id
        ≡⟨ cong g (sym (g-tt*-is-id tt*)) ⟩
      g (g tt*)
        ∎

    -- The universal element matches η_T:
    universal-element-is-η-T : universal-element ≡ η-hom T
    universal-element-is-η-T =
      universal-element
        ≡⟨ universal-element-is-g-g-tt* ⟩
      g (g tt*)
        ≡⟨ sym η-eq-T-proof ⟩
      η-hom T
        ∎
```

## 6. Upgrading to a Lawful `BasicFunctionalCategory`

When arrows in $C$ satisfy naturality with $\eta$ (which holds unconditionally for all pure arrows,
and holds for all arrows when effectful computations commute with pure constants—i.e. idempotency),
$C$ becomes a full `BasicFunctionalCategory`.

```agda
open import CoEndoYoneda using (BasicFunctionalCategory)

module LawfulBFC {ℓ : Level}
    (hsc : HSetCategory ℓ) 
    (ocf : ObjectConstrainedFunctor (SET ℓ) (HSetCategory.asCategory hsc) (λ Z → Z))
    (η-natural : ∀ {Y X : hSet ℓ} (f : HSetCategory.Hom hsc Y X)
               → let open PreFunctionalIO hsc ocf in 
                 let open HSetCategory hsc in
                 f ⋆ η-hom X ≡ η-hom Y ⋆ Functor.F-hom G f) where

  open PreFunctionalIO hsc ocf
  open HSetCategory hsc
  open ObjectConstrainedFunctor ocf

  η : NatTrans Id G
  η = record
    { N-ob = η-hom
    ; N-hom = η-natural
    }

  basicFunctionalCategoryIO : BasicFunctionalCategory C FF
  basicFunctionalCategoryIO = record
    { η = η
    ; η-eq-T = η-eq-T-proof
    }
```
