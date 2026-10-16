# CoEndoYoneda in Program Specification Based Programming (PSBP)

In `PSBP`, programs are effectful arrows between sets:
- Objects are sets: `ob = hSet ℓ`
- The functor `FF` is the identity on objects: `FF.F-ob Z = Z`
- `FF.F-hom = asProgram` lifts pure functions to programs

Restricting `FF` to be the identity on objects eliminates all object-level transports,
making every object $Y$ directly accessible to the point generator $g$.

Here we explore:
1. The definition of a `PSBPProgramCategory` where objects are sets.
2. The pure scaffolding without $\eta$: `PreFunctionalCategoryPSBP`.
3. The canonical construction of the natural transformation $\eta$ via `asProgram g`.
4. The proof that `η-eq-T` holds and equals the CoEndoYoneda `universal-element`.
5. The full CoEndoYoneda bijection in this PSBP setting.

```agda
{-# OPTIONS --cubical --guardedness #-}

module CoEndoYonedaPSBP where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets

open import CoEndoYoneda using (BasicFunctionalCategory; FunctionalCategory)

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

## 1. PSBP Program Category

A PSBP program category is a category whose objects are literally sets (`hSet ℓ`),
equipped with a functional embedding `asProgram` that is the identity on objects.

```agda
record PSBPProgramCategory {ℓ : Level} : Type (lsuc ℓ) where
  field
    program : hSet ℓ → hSet ℓ → Type ℓ
    isSetProgram : ∀ {Z Y} → isSet (program Z Y)
    identity : ∀ {Z} → program Z Z
    _>>>_ : ∀ {Z Y X} → program Z Y → program Y X → program Z X
    >>>-idL : ∀ {Z Y} (p : program Z Y) → identity >>> p ≡ p
    >>>-idR : ∀ {Z Y} (p : program Z Y) → p >>> identity ≡ p
    >>>-assoc : ∀ {Z Y X W} (p : program Z Y) (q : program Y X) (r : program X W)
              → (p >>> q) >>> r ≡ p >>> (q >>> r)

    asProgram : ∀ {Z Y} → (fst Z → fst Y) → program Z Y
    asProgram-id : ∀ {Z} → asProgram (λ (z : fst Z) → z) ≡ identity {Z}
    asProgram-seq : ∀ {Z Y X} (f : fst Z → fst Y) (g : fst Y → fst X)
                  → asProgram (λ z → g (f z)) ≡ asProgram f >>> asProgram g

  -- The underlying Category C:
  C : Category (lsuc ℓ) ℓ
  Category.ob C = hSet ℓ
  Category.Hom[_,_] C = program
  Category.isSetHom C = isSetProgram
  Category.id C = identity
  Category._⋆_ C = _>>>_
  Category.⋆IdL C = >>>-idL
  Category.⋆IdR C = >>>-idR
  Category.⋆Assoc C = >>>-assoc

  -- The functor FF is definitionally the identity on objects:
  FF : Functor (SET ℓ) C
  Functor.F-ob FF Z = Z
  Functor.F-hom FF = asProgram
  Functor.F-id FF = asProgram-id
  Functor.F-seq FF = asProgram-seq
```

## 2. Pre-Functional Category in PSBP

Here is the entire categorical apparatus:
- Terminal set `T = 1` and unique element `tt*`
- CoYoneda functor `CYF`
- CoEndo functor `CYEF`
- Global functor `G`
- Point generator `g`

Notice: **No $\eta$ and no $\mu$ are assumed.**

```agda
module PreFunctionalPSBP {ℓ : Level} (psbp : PSBPProgramCategory {ℓ}) where
  open PSBPProgramCategory psbp

  T : hSet ℓ
  T = (Unit* , isSetUnit*)

  tt* : fst T
  tt* = tt*

  CYF : hSet ℓ → Functor C (SET ℓ)
  CYF Z = record
    { F-ob = λ Y → (program Z Y , isSetProgram)
    ; F-hom = λ y2x → (λ z2y → z2y >>> y2x)
    ; F-id = funExt >>>-idR
    ; F-seq = λ y2x x2w → funExt (λ z2y → sym (>>>-assoc z2y y2x x2w))
    }

  CYEF : hSet ℓ → Functor C C
  CYEF Z = FF ∘F (CYF Z)

  -- G = CYEF T
  G : Functor C C
  G = CYEF T

  private
    module G = Functor G

  -- Global element generator:
  -- Takes an element z : fst Z and returns a program from T to Z.
  g : {Z : hSet ℓ} → fst Z → program T Z
  g z = asProgram (λ _ → z)
```

## 3. Canonical Construction of $\eta$ and Proof of `η-eq-T`

Because `FF` is the identity on objects, for **every** object $Y \in C$:
1. $Y$ is a set (`hSet ℓ`).
2. The point generator $g$ gives a function:
   $$g : \mathrm{fst } Y \longrightarrow \mathrm{program } T Y = \mathrm{fst } (G .F\text{-ob } Y)$$
3. Applying `asProgram` lifts this to a program from $Y$ to $G(Y)$:
   $$\eta_Y := \mathrm{asProgram}(g) \in \mathrm{program } Y (G(Y))$$

```agda
  -- Component of η for any object Y:
  η-hom : (Y : hSet ℓ) → program Y (G.F-ob Y)
  η-hom Y = asProgram g

  -- For Y = T, η-hom T is definitionally related to g (g tt*):
  η-eq-T-proof : η-hom T ≡ g (g tt*)
  η-eq-T-proof = 
    asProgram g
      ≡⟨ cong asProgram (funExt (λ (t : Unit*) → refl)) ⟩
    asProgram (λ _ → g tt*)
      ∎
```

## 4. The CoEndoYoneda Bijection in PSBP

Now suppose we consider the CoEndoYoneda bijection between:
$$\mathrm{NatTrans}(CYEF(Z), G \circ EF) \longleftrightarrow \mathrm{fst}((CYF \circ G \circ EF)(Z))$$

```agda
  module CoEndoEquivalencePSBP {EF : Functor C C} {Z : hSet ℓ} where
    private
      module EF = Functor EF
      module CYEF = Functor (CYEF Z)

    G∘EF : Functor C C
    G∘EF = G ∘F EF

    CYF∘G∘EF : Functor C (SET ℓ)
    CYF∘G∘EF = (CYF T ∘F G) ∘F EF

    fft2cyefz : program T (CYEF.F-ob Z)
    fft2cyefz = g identity

    τz→fz : NatTrans (CYEF Z) G∘EF → fst (CYF∘G∘EF.F-ob Z)
    τz→fz τz = fft2cyefz >>> N-ob τz Z
```

## 5. The Universal Element and its Identity with $\eta_T$

Taking $EF = \mathrm{Id}$ and $Z = T$:
1. The identity natural transformation `idG` from $G$ to $G \circ \mathrm{Id}$ is canonical.
2. The CoEndoYoneda forward map `τz→fz` sends `idG` to `universal-element`.
3. We prove unconditionally that:
   $$\mathrm{universal\text{-}element} \equiv g(\mathrm{identity}) \equiv g(g(\text{tt*})) \equiv \eta_T$$

```agda
  module UniversalOriginPSBP where
    open CoEndoEquivalencePSBP {EF = Id} {Z = T}

    idG : NatTrans (CYEF T) G∘EF
    idG = record
      { N-ob = λ _ → identity
      ; N-hom = λ f → 
          G.F-hom f >>> identity
            ≡⟨ >>>-idR (G.F-hom f) ⟩
          G.F-hom f
            ≡⟨ sym (>>>-idL (G.F-hom f)) ⟩
          identity >>> G.F-hom f
            ∎
      }

    universal-element : fst (CYF∘G∘EF.F-ob T)
    universal-element = τz→fz idG

    universal-element-is-g-id : universal-element ≡ g identity
    universal-element-is-g-id = >>>-idR fft2cyefz

    g-tt*-is-id : ∀ (t : fst T) → g t ≡ identity
    g-tt*-is-id t = 
      asProgram (λ _ → t)
        ≡⟨ cong asProgram (funExt (λ z → z)) ⟩
      asProgram (λ z → z)
        ≡⟨ asProgram-id ⟩
      identity
        ∎

    universal-element-is-g-g-tt* : universal-element ≡ g (g tt*)
    universal-element-is-g-g-tt* = 
      universal-element
        ≡⟨ universal-element-is-g-id ⟩
      g identity
        ≡⟨ cong g (sym (g-tt*-is-id tt*)) ⟩
      g (g tt*)
        ∎

    universal-element-is-η-T : universal-element ≡ η-hom T
    universal-element-is-η-T =
      universal-element
        ≡⟨ universal-element-is-g-g-tt* ⟩
      g (g tt*)
        ≡⟨ sym η-eq-T-proof ⟩
      η-hom T
        ∎
```

## 6. Full BasicFunctionalCategory and FunctionalCategory

When the programs in $C$ are pure (or when pure functions satisfy naturality),
$\eta$ forms a full natural transformation, making $C$ a lawful `BasicFunctionalCategory`.

```agda
  record LawfulPSBPEta : Type (lsuc ℓ) where
    field
      η-commute : ∀ {Y X : hSet ℓ} (p : program Y X)
                → p >>> η-hom X ≡ η-hom Y >>> G.F-hom p

    η : NatTrans Id G
    η = record
      { N-ob = η-hom
      ; N-hom = η-commute
      }

    asBasicFunctionalCategory : BasicFunctionalCategory C FF
    asBasicFunctionalCategory = record
      { η = η
      ; η-eq-T = η-eq-T-proof
      }
```
