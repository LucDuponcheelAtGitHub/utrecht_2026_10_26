# Program Specification Based Programming

This is project about a programming library, `PSBP`, that is a Domain Specific Language (DSL) for
the programming domain itself. 

Think about it as teaching a programming language what programming is all about.

I presented it at `Scala` eXchange (London) 2018 and flatMap (Oslo) 2019.

I presented it at a `Lean` Workshop (Reykjavic) 2025.

Recently I also ported the project partly to `Agda`.

This is work in progress.

The library strictly separates a pointfree, program specification based, Application Programmer
Interface (API) from a pointful, computation specification based, Library Developer Interface (LDI).

Think of programs as effectful functions.

Think of computations as effectful expressions.

Just like functions are, somehow, defined in terms of expressions, programs are, somehow, defined in
terms of computations.

Think of programs as closed components, with pointfree combinators.

For example `z2y >>> y2x >>> x2w`, where intermediate values `y` and `x` are invisible.

Think of computations as open components, with pointful combinators.

For example `cz >>= λ z → z→cy z >>= λ y → z&y→cx`, where intermediate values `z` and `y` are
visible.

## Ceci n'est pas une pipe

Well, yes, the well-known painting of René Magritte is not a pipe. 

It is some informal pipe description.

## This is not a program

```txt
thisIsNotAProgram = 
  IF isZero
  THEN one
  ELSE 
    LET minusOne >>> thisIsNotAProgram
    IN multiply
```

This is a program specification, a formal program description.

Nevertheless, "by abuse of language", I will use "program" instead of "program specification" and I
will use "code" for something text written in a programming language.

Any idea what the program may model?

`thisIsNotAProgram` uses a runtime environment.

The runtime environment starts with an argument `a`, continues with a pair `(a, v)`, where an
intermediate result is added to it as a value `v`, and ends with a triple `((a, v), r)`, where the
final result `r` is added to it. 

Notice that intermediate results, cfr. `LET p IN q` are not discarded as is done with `p >>> q`.

`PSBP` enables you to do positional programming, pointful programming in a pointfree way, replacing
names, like `a`, `v` and `r`, by their positions in the environment and using combinations of the
ones you need. 

For simple "script-like programs", positional programming is more convenient than pointfree
combinator based programming.

You may argue that positional programming is a step backwards, but pointful programming has to
invent names and it is not alway easy to find meaningful ones. For example, which one would you use
for `v` above? 

`PSBP` encourages writing mini script-like programs that combine more involved programs.

Compare this with the quote of Erik Meyer "good programmers write baby code".

## `PSBP`

```agda
{-# OPTIONS --guardedness #-}

module PSBP where
```

### `function`

I use `function Z Y` for the types of functions that are part of the programming DSL, in order to
distinguish them from the types of other functions that use standard `Z → Y` infix syntax.

```agda
function : Set₀ → Set₀ → Set₀
function Z Y = Z → Y
```

## The basic `program` capabilities involved

### Functions as programs

```agda
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)

record Functional 
    (program : Set₀ → Set₀ → Set₀) : Set₁ where
  field
    asProgram : 
        {Z Y : Set₀}
      → function Z Y 
      → program Z Y

  identity : {Z : Set₀} → program Z Z
  identity = asProgram (λ z → z)

  prj₁ :
      {Z Y : Set₀} 
    → program (Z × Y) Z
  prj₁ = asProgram proj₁

  prj₂ :
      {Z Y : Set₀} 
    → program (Z × Y) Y
  prj₂ = asProgram proj₂

  dupFunction :
      {Z : Set₀} 
    → function  Z (Z × Z)     
  dupFunction = λ z → (z , z)

  dup :
      {Z : Set₀} → program  Z (Z × Z)
  dup = asProgram dupFunction 

  branchFunction : 
      {Z : Set₀}
    → function (Z × Bool) (Z ⊎ Z)
  branchFunction (z , true)  = inj₁ z
  branchFunction (z , false) = inj₂ z

  branch : 
      {Z : Set₀} 
    → program (Z × Bool) (Z ⊎ Z)
  branch = asProgram branchFunction

open Functional {{...}}
```

Below are some examples that we use later.

```agda
open import Function.Base using (_∘_)

open import Data.Nat using (ℕ; _+_; _*_; zero; pred; suc)

_==_ : ℕ → ℕ → Bool
zero  == zero  = true
zero  == suc m = false
suc n == zero  = false
suc n == suc m = n == m

isZero : 
    {program : Set₀ → Set₀ → Set₀}
    {{_ : Functional program}} 
  → program ℕ Bool
isZero = asProgram (λ n → n == 0)

isOne : 
    {program : Set₀ → Set₀ → Set₀}
    {{_ : Functional program}}
  → program ℕ Bool
isOne = asProgram (λ n → n == 1)

one :
    {Z : Set₀}
    {program : Set₀ → Set₀ → Set₀}
    {{_ : Functional program}}
  → program Z ℕ
one = asProgram (λ _ → 1)

minusOne : 
    {program : Set₀ → Set₀ → Set₀}
    {{_ : Functional program}} 
  → program ℕ ℕ
minusOne = asProgram pred

minusTwo : 
    {program : Set₀ → Set₀ → Set₀}
    {{_ : Functional program}} 
  → program ℕ ℕ
minusTwo = asProgram (pred ∘ pred)

add :
    {program : Set₀ → Set₀ → Set₀} 
    {{_ : Functional program}}
  → program (ℕ × ℕ) ℕ
add = asProgram (λ (ln , rn) → ln + rn)

multiply :
    {program : Set₀ → Set₀ → Set₀} 
    {{_ : Functional program}} 
  → program (ℕ × ℕ) ℕ
multiply = asProgram (λ (ln , rn) → ln * rn)
```

### Sequential composition of programs.

```agda
record Sequential 
    (program : Set₀ → Set₀ → Set₀) : Set₁ where
  field
    andThen : 
        {Z Y X : Set₀}
      → program Z Y 
      → program Y X 
      → program Z X

  infixl 8 _>>>_

  _>>>_ : 
      {Z Y X : Set₀}
    → program Z Y 
    → program Y X 
    → program Z X
  lp >>> rp = andThen lp rp

open Sequential {{...}}
```

### Producing product data.

```agda
record Creational 
    (program : Set₀ → Set₀ → Set₀) : Set₁ where

  infixr 7 _\×/_

  field
    _\×/_ : 
        {Z Y X : Set₀}
        → program Z Y 
        → program Z X 
        → program Z (Y × X)

  infixr 7 _|×|_
  _|×|_ : 
      {Z Y X W : Set₀} 
      {{_ : Functional program}} 
      {{_ : Sequential program}} 
    → program Z X 
    → program Y W 
    → program (Z × Y) (X × W)
  lp |×| rp = (prj₁ >>> lp) \×/ (prj₂ >>> rp)

  infix 1 LET_IN_

  LET_IN_ :
      {{_ : Functional program}} 
      {{_ : Sequential program}} 
    → {Z Y X : Set₀} 
    → program Z Y → program (Z × Y) X → program Z X
  LET lp IN ip = (identity \×/ lp) >>> ip

open Creational {{...}}
```

`_\×/_`, `_|×|_` and `LET_IN_` above can be defined in terms of each other.

### Consuming sum data.

```agda
record Conditional 
    (program : Set₀ → Set₀ → Set₀) : Set₁ where

  infixr 6 _/+\_

  field
    _/+\_ : 
        {Z Y X : Set₀}
      → program Z X 
      → program Y X 
      → program (Z ⊎ Y) X

  infix 0 IF_THEN_ELSE_

  IF_THEN_ELSE_ :
      {{_ : Functional program}} 
      {{_ : Sequential program}} 
      {{_ : Creational program}} 
    → {Z Y : Set₀} 
    → program Z Bool 
    → program Z Y
    → program Z Y 
    → program Z Y
  IF bp THEN tp ELSE fp = 
    LET bp
    IN branch >>> (tp /+\ fp)

open Conditional {{...}}
```

`_/+\_` and `IF_THEN_ELSE_` above can be defined in terms of each other.

## `factorial`

```agda
{-# TERMINATING #-}
factorial : 
    {program : Set₀ → Set₀ → Set₀} 
    {{_ : Functional program}} 
    {{_ : Sequential program}} 
    {{_ : Creational program}} 
    {{_ : Conditional program}} 
  → program ℕ ℕ
factorial = 
  IF isZero 
  THEN one 
  ELSE 
    LET minusOne >>> factorial 
    IN multiply
```

## Statefulness

```agda
open import Data.Unit using (⊤)

record WithState 
    (S : Set₀) 
    (program : Set₀ → Set₀ → Set₀) : Set₁ where

  field
    readState  : {Z : Set₀} → program Z S
    
    writeState : program S ⊤

  modifyStateWith :
      {{_ : Functional program}} 
      {{_ : Sequential program}} 
      {{_ : Creational program}} 
    → {Z : Set₀} 
    → program S S 
    → program Z Z
  modifyStateWith p =
    LET readState >>> p >>> writeState
    IN prj₁

open WithState {{...}}
```

## Stateful program specification `statefulFactorial`

```agda
incrementState :
    {program : Set₀ → Set₀ → Set₀}
    {{_ : Functional program}}
    {{_ : Sequential program}}
    {{_ : Creational program}}
    {{_ : WithState ℕ program}} 
  → program ℕ ℕ
incrementState = modifyStateWith (asProgram suc)

{-# TERMINATING #-}
statefulFactorial :
    {program : Set₀ → Set₀ → Set₀}
    {{_ : Functional program}}
    {{_ : Sequential program}}
    {{_ : Creational program}}
    {{_ : Conditional program}}
    {{_ : WithState ℕ program}} 
  → program ⊤ ℕ
statefulFactorial =
  readState >>> factorial >>> incrementState

{-# TERMINATING #-}
statefulFactorialPair :
    {program : Set₀ → Set₀ → Set₀}
    {{_ : Functional program}}
    {{_ : Sequential program}}
    {{_ : Creational program}}
    {{_ : Conditional program}}
    {{_ : WithState ℕ program}} 
  → program ⊤ (ℕ × ℕ)
statefulFactorialPair = 
  statefulFactorial \×/ statefulFactorial
```

## `fibonacci`

```agda

{-# TERMINATING #-}
fibonacci : 
    {program : Set₀ → Set₀ → Set₀} 
    {{_ : Functional program}} 
    {{_ : Sequential program}} 
    {{_ : Creational program}} 
    {{_ : Conditional program}}
  → program ℕ ℕ
fibonacci =  
  IF isZero 
  THEN one 
  ELSE
    IF isOne 
    THEN one 
    ELSE 
             (minusOne >>> fibonacci 
          \×/ minusTwo >>> fibonacci) 
      >>> add
```

Notice that we could have used a `LET_IN_` instead of `_\×/_` and we could have used
`_/+\_` instead of `IF_THEN_ELSE_`. It is all about *elegance* of code rather than
*power of expression* of code. 

Of course, elegance is a subjective notion.

`LET`, `IN`, `IF`, `THEN` and `ELSE` are, maybe, more elegant for computer scientists
(they can be thought of as library level keywords).

`>>>`, `_/+\_` and `\×/` are, maybe, more elegant for mathematicians.

## Parallelism

As far as their types are concerned sequential products and parallel products do not differ.

Parallelism could be considered to be an implementation choice, but we consider it to be a
specification decision, allowing for an hybrid approach.

```agda
record WithPar 
    (program : Set₀ → Set₀ → Set₀) : Set₁ where

  infixr 7 _||×||_

  field
    _||×||_ : 
        {Z Y X W : Set₀} 
      → program Z X 
      → program Y W 
      → program (Z × Y) (X × W)

  infixr 7 _\\×//_
  
  _\\×//_ : 
        {Z Y X : Set₀}
        {{_ : Functional program}}
        {{_ : Sequential program}}
        {{_ : Creational program}}
      → program Z Y 
      → program Z X 
      → program Z (Y × X)
  lp \\×// rp = dup >>> (lp ||×|| rp)

open WithPar {{...}}
```

Notice that, for parallelism, we declared `_||×||_` and defined `_\\×//_`
(using `dup`), while, for products, we declared `_\×/_` and defined `_|×|_`
(using `prj₁` and `prj₂`). 

All four possibilities are essentially equivalent.

## `parallelFibonacci`

```agda
{-# TERMINATING #-}
parallelFibonacci :
    {program : Set₀ → Set₀ → Set₀}
    {{_ : Functional program}}
    {{_ : Sequential program}}
    {{_ : Creational program}}
    {{_ : Conditional program}}
    {{_ : WithPar program}}
  → program ℕ ℕ
parallelFibonacci =
  IF isZero 
  THEN one
  ELSE
    IF isOne 
    THEN one
    ELSE
               (minusOne >>> fibonacci 
          \\×// minusTwo >>> fibonacci) 
      >>> add
```

The difference between `fibonacci` and `parallelFibonacci` is that the former uses `_\×/_`
while the latter uses `_\\×//_`. Of course we are specifying here ... , implementing the
combinators involved is another matter. I implemented parallelism using the `Drama` actor
library. Working with actors gives you a lot of low-level power to write parallel programs,
but writing them so that they are correct is also another matter. Therefore it is, imho, more
conventient to offer a high-level pointfree combinator API and leave the heavy lifting on
how to implement it to library developers.

Below are two (commented out) alternative ways to define the `ELSE` part of `parallelFibonacci`.

```agda
    --       (minusOne \×/ minusTwo) 
    --   >>> (parallelFibonacci ||×|| parallelFibonacci)
    --   >>> add

    --       (minusOne \\×// minusTwo) 
    --   >>> (parallelFibonacci ||×|| parallelFibonacci)
    --   >>> add
```

I can show `fibonacci` and `parallelFibonacci` at runtime. 

Using `htop` one can see that the latter uses all available processing capabilities.

The implementation of `_||×||_` uses the Drama actor library.

Parallel programming directly with actors is notoriously hard. 

Thanks for listening!










