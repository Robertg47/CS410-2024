{-# OPTIONS --guardedness #-}

open import Data.String.Base using (String)
open import Data.Char.Base
open import IO.Base 
open import IO.Finite using (getLine)
open import IO.Effectful
open import IO.Instances

------------------------------------------------------------------------
-- Coursework 1: Cellular (100 marks, 40% of course total)
--
-- The goal of this coursework is to write a small one dimensional
-- cellular automaton that traces a rule (e.g. rule 90 [1]) on an
-- initial state.
--
-- For that we are going to introduce some fancy types making explicit
-- the notion of sliding window that arises naturally during the
-- implementation.
--
-- [1] https://en.wikipedia.org/wiki/Rule_90
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Submission
--
-- Remember that this is submitted by creating a *private* repository
-- on either github or the departmental gitlab and inviting me so that
-- I can mark your work.
--
-- Deadline: Thursday 15 February at 5pm
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Workflow
--
-- If you find below some concepts or syntax we have not yet seen, don't
-- hesitate to skip the questions and complete other problems further
-- down the file.
-- You can come back to the questions you skipped once we have covered
-- the related material in the lectures.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Marks
--
-- Boolean functions     5   MARKS   -- 5 - 5
-- Equality relation     1   MARK    -- 1 - 6
-- First proofs          6   MARKS   -- 6 - 12
-- Natural numbers       13  MARKS   -- 13 - 25
-- Forwards lists        11  MARKS   -- 11- 36
-- Backwards lists       13  MARKS   -- 13 - 49
-- Combining lists       2   MARKS   -- 2  - 51
-- Quantifiers           9   MARKS   -- 9  - 60
-- Membership            15  MARKS   -- 15  - 75
-- Cellular automaton    10  MARKS   -- 10   - 85
-- Extension             15  MARKS
--
-- TOTAL                 100 MARKS

------------------------------------------------------------------------
-- Warming up: data, functions, proofs
------------------------------------------------------------------------

-- what does it mean a (safe!) function in quantifiers?

-- We will be mentioning a Set or two, so let declare variables for them
variable A B C D : Set


------------------------------------------------------------------------
-- Boolean functions (5 MARKS)

-- The cells in a cellular automata only have two possible states: alive
-- or dead. We will be using the booleans as our representation of these
-- two states (true ↦ alive; false ↦ dead).
-- To describe various rules, it is convenient to have some basic functions
-- acting on booleans. So let us get started with them.

-- The type of booleans has two constructors: true and false
data Bool : Set where
  true : Bool
  false : Bool

-- (1 MARK)
-- Implement boolean negation
not : Bool → Bool
not true = false
not false = true


-- (1 MARK)ot
-- Implement boolean conjunction
_∧_ : Bool → Bool → Bool
true ∧ y = y
false ∧ x₁ = false


-- (1 MARK)
-- Implement boolean disjunction
_∨_ : Bool → Bool → Bool
true ∨ x₁ = true
false ∨ y = y

-- (1 MARK)
-- Implement boolean exclusive or
_xor_ : Bool → Bool → Bool
true xor y = not y
false xor y = y

-- (1 MARK)
-- Implement if then else
infix 0 if_then_else_
if_then_else_ : Bool → A → A → A
if true then x1 else x2 = x1
if false then x1 else x2 = x2

------------------------------------------------------------------------
-- Equality relation (1 MARK)

-- In order to have some unit tests or to prove some properties of our
-- functions, we are going to need propositional equality as well as
-- some related functions and concepts.

-- Propositional equality is the inductive family with a single
-- constructor insisting that both of its indices are equal on the
-- nose.
infix 0 _≡_
data _≡_ (a : A) : A → Set where
  refl : a ≡ a

-- Equality is symmetric
symmetric : ∀ {x y : A} → x ≡ y → y ≡ x
symmetric refl = refl

-- Equality is transitive
transitive : ∀ {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transitive refl eq = eq

-- If `x` is equal to `y` then applying `f` to one is indistinguishable
-- from apply it to the other. Prove it.
cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

-- The empty type has no constructor. There are no closed proof of it.
-- It is a useful encoding of impossibility.
data ⊥ : Set where

-- From the empty type we can conclude anything: the context we are in
-- is simply absurd.
⊥-elim : ⊥ → A
⊥-elim ()

-- Two terms `x` and `y` are distinct precisely when assuming that there
-- are equal leads to a contradiction i.e. a proof of the empty type.
_≢_ : (x y : A) → Set
x ≢ y = x ≡ y → ⊥

-- (1 MARK)
-- For instance: true and false are not equal!
-- how is the assumption happening ? ========================================
_ : true ≢ false
_ = \ ()


--------------------------------------------------------------------------
-- First proofs (6 MARKS)

-- (1 MARK)
-- Prove that boolean negation is involutive -- why is it only boolean negation??
not-involutive : ∀ b → not (not b) ≡ b
not-involutive true = refl
not-involutive false = refl

-- (1 MARK)
-- Prove that boolean negation is not the identity function
not-not-id : ∀ b → not b ≢ b
not-not-id true ()
not-not-id false ()

-- Prove the following de Morgan laws.
-- Bonus for style: good operator definitions can lead to short proofs

-- (2 MARKS)
not-and : ∀ b c → not (b ∧ c) ≡ not b ∨ not c
not-and true c = refl
not-and false c = refl

-- (2 MARKS)
not-or : ∀ b c → not (b ∨ c) ≡ not b ∧ not c
not-or true c = refl
not-or false c = refl

--------------------------------------------------------------------------
-- Natural numbers (13 MARKS)

-- The inductive type of natural numbers

open import Data.Nat.Base using (ℕ ; zero ; suc)

variable m n : ℕ

-- (1 MARK)
-- Implement addition by recursion on the first argument
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

-- (1 MARK)
-- Prove that `_+_` commutes with `suc`
+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

-- (1 MARK)
-- Prove that addition is a monoid
zero-+ : ∀ m → zero + m ≡ m
zero-+ m = refl
-- (1 MARK)
-- +-zero zero = refl
-- +-zero (suc m) = {!+-zero m!}
+-zero : ∀ m → m + zero ≡ m
+-zero zero = refl
+-zero (suc m) = cong suc (+-zero m)

meqn->smeqsn : ∀ {x y : ℕ} → x ≡ y → (suc x) ≡ (suc y)
meqn->smeqsn {x} {x} refl = refl

two-zeroes : ∀ m →  zero + m ≡ m + zero
two-zeroes zero = refl
two-zeroes (suc m) = cong suc (two-zeroes m)

two-zeroes-rev : ∀ m →  m + zero ≡ zero + m
two-zeroes-rev zero = refl
two-zeroes-rev (suc m) = cong suc (two-zeroes-rev m)

-- (3 MARKS)
-- hint: +-suc could be useful
+-commutative : ∀ m n → m + n ≡ n + m
+-commutative m zero = two-zeroes-rev m
+-commutative m (suc n) = transitive (+-suc m n) (meqn->smeqsn (+-commutative m n))

-- (1 MARK)
+-associative : ∀ m n p → (m + n) + p ≡ m + (n + p)
+-associative zero n p = refl
+-associative (suc m) n p = cong suc (+-associative m n p)

-- (1 MARK)
-- Prove that suc is injective
suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective {m} {.m} refl = refl

-- The sum type
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- (1 MARK)
-- Implement bimap
bimap : (A → C) → (B → D) → A ⊎ B → C ⊎ D
bimap f g (inj₁ x) = inj₁ (f x)
bimap f g (inj₂ x) = inj₂ (g x)


m!=n->sm!=sn : ∀ {x y : ℕ} → x ≢ y → (suc x) ≢ (suc y)
m!=n->sm!=sn {zero} {zero} x1 x2 = x1 refl
m!=n->sm!=sn {suc x} {suc x} x1 refl = x1 refl


-- assumptions ^
-- suc x != suc y, suc x = suc y
-- refl suc x = suc y -> suc x = suc x   ->   suc x != suc x AND suc x = suc x -> _|_

--m!=n->sm!=n : ∀ {x y : ℕ} → x ≢ y → (suc x) ≢ y
--m!=n->sm!=n {zero} {zero} x1 x2 = x1 refl
--m!=n->sm!=n {x} {.(suc x)} x1 refl = {!!}

-- (3 MARKS)6
-- Prove that equality of natural numbers is decidable
≡-dec : (m n : ℕ) → (m ≡ n) ⊎ (m ≢ n)
≡-dec zero zero = inj₁ refl
≡-dec zero (suc n) = inj₂ \ ()
≡-dec (suc m) zero = inj₂ \ ()
≡-dec (suc m) (suc n) = bimap meqn->smeqsn m!=n->sm!=sn (≡-dec m n)

--------------------------------------------------------------------------
-- Lists
-- The state of a cellular automaton can be represented using a list of
-- cells. Let us introduce two types of lists (forwards denoted using `>`,
-- and backwards denoted using `<`) and some operations over them.
-- As a sanity check we will also prove some of these operations' properties.


------------------------------------------------------------------------
-- Forwards lists (11 MARKS)

-- A forwards list is held from its left end and processed left-to-right
-- e.g. in [>1,2,3] the first element is 1, the second 2, etc.

-- Mnemonic: _,-_ has the dash pointing towards the tail
infixr 5 _,-_
data List> (A : Set) : Set where
  [] : List> A
  _,-_ : A → List> A → List> A

-- (1 MARK)
-- Give the list [>1,2,3]
[>1,2,3] : List> ℕ
[>1,2,3] =  1 ,- 2 ,- 3 ,- []

-- (1 MARK)
-- Give the list [>4,5,6]
[>4,5,6] : List> ℕ
[>4,5,6] = 4 ,- 5 ,- 6 ,- []

variable
  xs ys zs : List> A
--
---- We will be using the same name for the same operations over forwards
---- and backwards so we need to put them in a module. This mean all of
---- the List>-related definition should be indented to be in this inner
-- module.
module List>P where

  -- Programs

  -- (1 MARK)
  -- Implement `replicate` the function that takes a natural number and
  -- a value and returns a list containing `n` copies of the value.
  replicate : ℕ → A → List> A
  replicate zero x₁ = []
  replicate (suc x) x1 = x1 ,- (replicate x x1)

  -- (1 MARK)
  -- Implement the length operation, it counts the number of elements
  -- in the list
  length : List> A → ℕ
  length [] = zero
  length (x ,- x1) = suc (length x1)


  tail : List> A -> List> A
  tail [] = []
  tail (x ,- t) = t


  -- (1 MARK)
  infixr 6 _++_
  -- Append combines the content of two forwards list in an order-respecting
  -- manner e.g. [>1,2,3] ++ [>4,5,6] computes to [>1,2,3,4,5,6].
  -- Feel free to add unit tests
  _++_ : List> A → List> A → List> A
  [] ++ x2 = x2
  (x ,- x1) ++ x2 = x ,- (x1 ++ x2)

-- 3 2 1 h ,  6 5 4 h

  concattest : List> ℕ
  concattest = ([>1,2,3] ++ [>4,5,6])


  -- (1 MARK)
  -- Implement `map` which, given a function from `A` to `B` and a `List> A`,
  -- applies the function to every element in the list thus creating a `List> B`.
  map : (A → B) → List> A → List> B
  map f [] = []
  map f (head ,- tail) = f head ,- (map f tail)

  -- Proofs
  -- (1 MARK)
  -- Prove that the `length` of the list obtained by calling `replicate`
  -- is the size given as an input.
  length-replicate : (n : ℕ) (x : A) → length (replicate n x) ≡ n
  length-replicate zero x = refl
  length-replicate (suc n) x = cong suc (length-replicate n x)

-- given: length (replicate n x) ≡ n
-- need: length(replicate (suc n) x = suc n
-- how did it deduce that
-- length(replicate(suc n) x) == suc (length(replicate n x))

-- (replicate suc n x) = h : (replicate n x)
-- length h : (replicate n x) = suc (length(replicate n x))

  right+zero : ∀ m → m ≡ m + zero
  right+zero zero = refl
  right+zero (suc m) = cong suc (right+zero m)

  simplify : (xs : List> A) → length (xs ++ []) ≡ length xs + zero
  simplify [] = refl
  simplify (x ,- xs) = cong suc (simplify xs)

  prove : ∀ m n → suc (m + n) ≡ m + suc n
  prove m n = symmetric (+-suc m n)

  -- (1 MARK)
  -- Prove that length distributes over append
  length-++ : (xs ys : List> A) → length (xs ++ ys) ≡ length xs + length ys
  length-++ [] ys = refl
  length-++ (x ,- xs) ys = cong suc (length-++ xs ys)

 -- length-++ xs (x ,- ys) = {!transitive (meqn->smeqsn (length-++ xs ys)) (prove (length xs) (length ys))!}

  -- have: length (xs ++ []) = length xs + length []
  -- need: equality

  -- have: length (xs ++ ys) ≡ length xs + length ys
  -- have: suc (length (xs ++ ys) = suc (length xs + length ys)
  -- have: trans -> suc (length (xs ++ ys) = suc (length xs + length ys) ->

  -- need: suc (length (xs ++ y,-ys))) ≡ (length xs + length y,-ys)

  -- (1 MARK)
  -- Prove that append is associative
  ++-assoc : (xs ys zs : List> A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = refl
  ++-assoc (x ,- xs) ys zs = cong (λ n → x ,- n) (++-assoc xs ys zs)

  -- (2 MARKS)
  -- State and prove another property. I can think of various ones e.g.
  -- length-map, replicate-+, map-++, map-map whose names are hopefully
  -- suggestive enough.

  -- replicate distribution over concatenation
  replicate-+ : (m n : ℕ) (a : A) → replicate(m + n) a ≡ (replicate m a) ++ (replicate n a)
  replicate-+ zero n a = refl
  replicate-+ (suc m) n a = cong (\ n → a ,- n) (replicate-+ m n a)

-- have: replicate(m + n) a ≡ (replicate m a) ++ (replicate n a)
-- have: a ,- relicate (m + n) a = a ,- replicate m a ++ replicate n a

-- goal: replicate (suc m + n) a ≡ replicate (suc m) a ++ replicate n a
-- goal: replicate (suc(m+n)) a = a ,- replicate m a ++ replicate n a
-- goal: a ,- relicate (m + n) a = a ,- replicate m a ++ replicate n a

--------------------------------------------------------------------------
-- Backwards lists (13 MARKS)

-- A backwards list is held from its right and processed righ-to-left
-- e.g. in [<1,2,3] the first element is 3, the second 2, etc.

infixl 5 _-,_
data List< (A : Set) : Set where
  [] : List< A
  _-,_ : List< A → A → List< A

-- (1 MARK)
-- Give the list [<1,2,3]
[<1,2,3] : List< ℕ
[<1,2,3] = [] -, 1 -, 2 -, 3

-- (1 MARK)
-- Give the list [<4,5,6]
[<4,5,6] : List< ℕ
[<4,5,6] = [] -, 4 -, 5 -, 6

variable
  sx sy sz : List< A

-- Implement here the same operations and proofs we had for backwards list
-- length-++ is 3 MARKS here
module List<P where

  -- Programs

  -- (1 MARK)
  -- Creating a backwards list
  replicate : ℕ → A → (List< A)
  replicate zero x = []
  replicate (suc x) elem = (replicate x elem) -, elem

  -- (1 MARK)
  -- The length of a list is its number of elements
  length : List< A → ℕ
  length [] = zero
  length (tail -, head) = suc (length tail)

  -- (1 MARK)
  -- Combining two backwards lists
  _++_ : List< A → List< A → List< A
  x ++ [] = x
  x ++ (y -, h) = (x ++ y) -, h

  -- [empty>1,2,3] ++ [empty>4,5,6] = [empty>1,2,3,4,5,6]

  concatTest : List< ℕ
  concatTest = ([<1,2,3] ++ [<4,5,6])

  -- (1 MARK)
  -- Modifying a backwards list
  map :(A → B) → List< A → List< B
  map f [] = []
  map f (list -, x) = (map f list) -, (f x)

  -- Proofs

  -- (1 MARK)
  length-replicate : (n : ℕ) (x : A) → length (replicate n x) ≡ n
  length-replicate zero x = refl
  length-replicate (suc n) x = cong suc (length-replicate n x)

  simplify : (xs : List< A) → length (xs ++ []) ≡ length xs + zero
  simplify [] = refl
  simplify (xs -, x) = cong suc (simplify xs)

  -- (3 MARKS)
  length-++ : (xs ys : List< A) → length (xs ++ ys) ≡ length xs + length ys
  length-++ xs [] = simplify xs
  length-++ xs (ys -, x) = transitive (cong suc (length-++ xs ys)) (symmetric (+-suc (length xs) (length ys)))

-- have: length (xs ++ ys) ≡ length xs + length ys
-- have: suc(length (xs ++ ys) = suc (length xs + length ys)
-- have: suc(length (xs ++ ys) = length xs + suc(length ys)

-- need: length (xs ++ ys-,y) ≡ length xs + (length ys-,y)
-- need: length (xs ++ ys -, y) = length xs + suc (length ys)
-- need: suc (length xs ++ ys) = length xs + suc (length ys)

  -- (1 MARK)
  ++-assoc : (xs ys zs : List< A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc xs ys [] = refl
  ++-assoc xs ys (zs -, x) = cong (\ n -> n -, x) (++-assoc xs ys zs)

  -- (2 MARKS)
  -- State and prove a (different!) property of your own once again.

  _∘_ : (f : B → C) (g : A → B) → (A → C)
  (f ∘ g) x = f (g x)

  map-compose : ∀ {A B C : Set} (f : B → C) (g : A → B) (xs : List< A) → map (f ∘ g) xs ≡ map f (map g xs)
  map-compose f g [] = refl
  map-compose f g (xs -, x) = cong (\ n → n -, (f (g x))) (map-compose f g xs)

  -- have: map (f ∘ g) xs ≡ map f (map g xs)
  -- have: map (f ∘ g) xs -, f (g x) = map f (map g xs) -, f (g x))

  -- need: map (f ∘ g) (xs -, x) ≡ map f (map g (xs -, x))
  -- need: map (f ∘ g) xs -, f (g x) = map f (map g xs) -, (g x)
  -- need: map (f ∘ g) xs -, f (g x) = map f (map g xs) -, f (g x))

--------------------------------------------------------------------------
-- Combining different kinds of lists (2 MARKS)

-- There are two ways to combine [<1,2,3] and [>4,5,6] in a way that
-- respects the elements' ordering depending on whether we return a
-- forwards or a backwards list.


-- Mnemonic: _<><_ takes a backwards (<) and a forwards (>) list and
-- returns a backwards one (<)

infixl 5 _<><_

-- (1 MARK)
-- Implement fish
_<><_ : List< A → List> A → List< A
x <>< [] = x
x <>< (h ,- tail) =  (x -, h) <>< tail

-- Unit test
combinationtest1 : List< ℕ
combinationtest1 = [<1,2,3] <>< [>4,5,6]
_ : [<1,2,3] <>< [>4,5,6] ≡ [] -, 1 -, 2 -, 3 -, 4 -, 5 -, 6
_ = refl

-- Mnemonic: _<>>_ takes a backwards (<) and a forwards (>) list and
-- returns a forwards one (>)

infixr 5 _<>>_

convertList : List< A -> List> A
convertList [] = []
convertList (tail -, h) = (List>P._++_ (convertList tail) (h ,- []))

-- (1 MARK)
-- Implement chips
_<>>_ : List< A → List> A → List> A
[] <>> y = y
(tail -, x) <>> y = tail <>> (x ,- y)

-- Unit test
combinationtest2 : List> ℕ
combinationtest2 = [<1,2,3] <>> [>4,5,6]
_ : [<1,2,3] <>> [>4,5,6] ≡ 1 ,- 2 ,- 3 ,- 4 ,- 5 ,- 6 ,- []
_ = refl



--------------------------------------------------------------------------
---- Getting ready: Quantifiers, Focus
--------------------------------------------------------------------------

variable
  P Q : A → Set
  x : A

------------------------------------------------------------------------
-- The universal quantifier for forward lists (9 MARKS)
-- (you could define a similar thing for backward lists but we will not
-- need it here)

-- `All> P xs` states that `P` holds of all the elements in `xs`.
-- The proofs of that statement are:

-- `[]` is the trivial proof that when `xs = []`, the statement is vacuously true.
-- `_,-_` packs together a proof that `P x` holds and that `All> P xs` holds to
-- conclude that `All> P (x ,- xs)` holds.

data All> (P : A → Set) : List> A → Set where
  []   : All> P []
  _,-_ : P x → All> P xs → All> P (x ,- xs)

module All>P where

  -- (1 MARK)
  -- A (safe!) head function extracting a proof that `P x` holds when
  -- we know that `P` holds of all of the elements in `x ,- xs`
  head : All> P (x ,- xs) → P x
  head (x ,- x₁) = x


  -- (1 MARK)
  -- A (safe!) tail function building a proof that `P` holds of all
  -- the elements in `xs` when we already know that it holds of all
  -- of the elements in `x ,- xs`
  tail : All> P (x ,- xs) → All> P xs
  tail (x ,- tail) = tail

  -- (1 MARK)
  -- If the P implies Q and P holds of all the elements in xs then
  -- Q also does!
  map : (∀ {x} → P x → Q x) → All> P xs → All> Q xs
  map x [] = []
  map x (h ,- tail) = x h ,- (map x tail)

-- A `List> A` can be seen as giving an element of type `A` for every
-- element in `xs`. Conversely, if we have an element of a type `B` for
-- every element in `xs` then we have a list of `B`s.
-- `fromList>` and `toList>` witness this. Additionally, we expect them
-- `toList>` to be a left inverse to `fromList>`.

-- (2 MARKS)
-- Implement `fromList>`
fromList> : (xs : List> A) → All> (λ _ → A) xs
fromList> [] = []
fromList> (x ,- xs) = x ,- fromList> xs

-- (2 MARKS)
-- Implement `toList>`
toList> : All> (λ _ → B) xs → List> B
toList> [] = []
toList> (x ,- tail) = x ,- toList> tail

-- (1 MARK)
-- Prove that `toList>` and `map` commute!
toList>-map : (f : A → B) (xs : All> (λ _ → A) xs) →
              toList> (All>P.map f xs) ≡ List>P.map f (toList> xs)
toList>-map f [] = refl
toList>-map f (x ,- xs) = cong (\ n -> f x ,- n) (toList>-map f xs)

-- (1 MARK)
-- Prove that `toList>` is a left inverse to `fromList>`
from-to-List> : (xs : List> A) → toList> (fromList> xs) ≡ xs
from-to-List> [] = refl
from-to-List> (x ,- xs) = cong (\ n -> x ,- n) (from-to-List> xs)

--------------------------------------------------------------------------
-- Membership as a context-revealing view (15 MARKS)

-- The following definition is a membership predicate: it states that
-- `x` belongs to `as` (written `x ∈ as`) whenever we can find a way
-- to take `as` apart into:
--   1. a backwards list `sx` acting as a prefix
--   2. the element `x` itself
--   3. a forwards list `xs` acting as a suffix

infix 1 _∈_
infix 3 _[_]_
data _∈_ {A : Set} :  A → List> A → Set where
  _[_]_ : (sx : List< A) (x : A) (xs : List> A) → x ∈ (sx <>> x ,- xs)

-- (2 MARKS)
-- Prove that membership is a proof-relevant notion i.e.
-- you can have two proofs that have the same type and
-- are not equal. Keep it as simple as possible!
proof-relevant :
  let x : ℕ
      x = 2
      xs : List> ℕ
      xs = 1 ,- 2 ,- 3 ,- 2 ,- []
      p : x ∈ xs
      p = ([] -, 1) [ x ] (3 ,- 2 ,- [])
      q : x ∈ xs
      q = ([] -, 1 -, 2 -, 3) [ 2 ] ([])
  in p ≢ q
proof-relevant ()


reduce : (sx : List< A) (xs : List> A) -> All> P (sx <>> xs) -> All> P xs
reduce [] xs x = x
reduce (tail -, head) xs x = All>P.tail (reduce tail (head ,- xs) x)

-- HARD (4 MARKS):
-- Prove that if `x` belongs to ‵xs` and `P` holds of all the elements
-- in `xs` then `P x` also holds. This will require coming up with the type
-- of a tricky auxiliary lemma!
lookup : x ∈ xs → All> P xs → P x
lookup ([] [ y ] xs) quantifier = All>P.head quantifier
lookup (sx [ y ] xs) quantifier = All>P.head (reduce sx (y ,- xs) quantifier)


-- Interlude: We can say that a list `xs` is focused if we have a `focus`
-- together with a proof that it belongs to `xs` i.e. that we have a split
-- of `xs` of the form `prefix <>> focus ,- suffix`.
infix 1 !_
record Focused (xs : List> A) : Set where
  constructor !_
  field
    {focus} : A
    member : focus ∈ xs

-- (1 MARK)
-- Write the function that slides the focus one step to the left if possible
-- and behaves like the identity otherwise.
leftwards : Focused xs → Focused xs
leftwards (! [] [ _ ] xs) = ! [] [ _ ] xs
leftwards (! sx -, x [ _ ] xs) = ! sx [ x ] _ ,- xs

-- (1 MARK)
-- Same but for sliding one step to the right.
rightwards : Focused xs → Focused xs
rightwards (! sx [ y ] []) = ! sx [ y ] []
rightwards (! sx [ y ] (x ,- xs)) = ! (sx -, y [ x ] xs)


-- (2 MARKS)
-- Prove that it is *not* the case that leftwards and rightwards are inverses
-- Keep it as simple as possible!
counter-example :
  let xs : List> ℕ
      xs = 1 ,- 2 ,- 3 ,- []
      f : Focused xs
      f = ! (([] -, 1 -, 2) [ 3 ] [])
  in leftwards (rightwards f) ≢ f
counter-example = λ ()
--
---- (1 MARK)
---- Write the function that takes a list of boolean corresponding to left/right
---- instructions (true ↦ left; false ↦ right) and repeatedly moves the focus
---- according to it
following : List> Bool → Focused {A} xs → Focused xs
following [] y = y
following (true ,- list) state = leftwards state
following (false ,- list) state = rightwards state
--
--{- uncomment the unit test
_ : following (true ,- true ,- false ,- []) (! ([<1,2,3] [ 0 ] [>4,5,6]))
  ≡ ! [] -, 1 -, 2 [ 3 ] 0 ,- 4 ,- 5 ,- 6 ,- []
_ = refl
-- CLOSINGBRACKET


-- HARD (4 MARKS)
-- Prove that for every element in a list we can create a focus around it.

focusUltimateHelper : (sx : List< A)(xs : List> A)  → All> (_∈ sx <>> xs) xs
focusUltimateHelper sx [] = []
focusUltimateHelper sx (x ,- xs) =  (\ x -> (sx [ x ] xs)) x ,- (focusUltimateHelper (sx -, x) xs)

focus : (xs : List> A) → All> (_∈ xs) xs
focus = focusUltimateHelper []

--{-
-- Unit test for focus
_ : focus [>1,2,3] ≡ ([] [ 1 ] 2 ,- 3 ,- []) ,- -- 1 in focus
                     ([] -, 1 [ 2 ] 3 ,- []) ,- -- 2 in focus
                     ([] -, 1 -, 2 [ 3 ] []) ,- -- 3 in focus
                     []
_ = refl
--CLOSINGBRACKET

--------------------------------------------------------------------------
---- And now: a cellular automaton! (10 MARKS)
--------------------------------------------------------------------------
--
---- A rule from `A` to `B` is a function that, given a `List> A` and an
---- element that belongs to it, produces a value of typen `B`.
Rule : Set → Set → Set
Rule A B = ∀ {x : A} {xs : List> A} → x ∈ xs → B
--
---- Here is an example of a rule returning the left neighbour
---- of the current focus (if it exists) and the default value
---- otherwise.

left-neighbour : A → Rule A A
left-neighbour default (_ -, l [ x ] _) = l -- l is on the left of the focus
left-neighbour default ([] [ x ] xs) = default -- nothing is on the left: default!
--

---- (3 MARKS)
-- Implement `step`, the function which applies a rule to every element
-- in an initial `List> A`.

--helper .[] x [] = []
--helper (_ ,- _) rule (belongs ,- qualifier) = {!rule belongs ,- (helper (_ ,- _) rule qualifier)!}

construct : (xs ys : List> A) → Rule A B -> All> (_∈ ys) xs -> List> B
construct .[] ys rule [] = []
construct (h ,- t) ys rule (x ,- qualifier) =  (rule x) ,- (construct t ys rule qualifier)

step : Rule A B → List> A → List> B
step x list =  (construct list list x (focus list))


-- The left neighbour rule with default value 17 deployed over [>1,2,3]
_ : step (left-neighbour 17) [>1,2,3] ≡ 17 ,- 1 ,- 2 ,- []
_ = refl
--
---- Rules such as rule 90 (https://en.wikipedia.org/wiki/Rule_90) are more
---- restricted: they operate on a sliding window of size 3 (one element to
---- the left of the focus, the focus, and one element to its right).
---- Such windows can be represented by the following record type.
record Window : Set where
  constructor _,_,_
  field
    left : Bool
    middle : Bool
    right : Bool

-- (1 MARK)
-- Write the function turning a membership proof into the appropriate window.
-- Pad the missing cells with `false`.
pad : Rule Bool Window
pad ([] [ focus ] []) = false , focus , false
pad ([] [ focus ] x ,- xs) = false , focus , x
pad (sx -, x [ focus ] []) = x , focus , false
pad (sx -, x [ focus ] y ,- xs) = x , focus , y

-- (1 MARK)
-- Implement `rule`, the function turning a window-consuming boolean
-- function into a Rule.
rule : (Window → Bool) → Rule Bool Bool
rule table rule = table (pad rule)

---- Implement (at least) rule 90, 30, and 110.
---- https://en.wikipedia.org/wiki/Rule_90
---- https://en.wikipedia.org/wiki/Rule_30
---- https://en.wikipedia.org/wiki/Rule_110


-- (1 MARK)
rule90 : Rule Bool Bool
rule90 = rule λ x → (Window.left x) xor (Window.right x)


ruletest : Rule Bool Bool
ruletest = rule λ x → true

---- (1 MARK)
rule30 : Rule Bool Bool
rule30 = rule (λ x →  Window.left x xor (Window.middle x  ∨ Window.right x))

rule110WindowConsumer : Window -> Bool
rule110WindowConsumer (true , true , true) = false
rule110WindowConsumer (true , true , false) = true
rule110WindowConsumer (true , false , true) = true
rule110WindowConsumer (true , false , false) = false
rule110WindowConsumer (false , true , true) = true
rule110WindowConsumer (false , true , false) = true
rule110WindowConsumer (false , false , true) = true
rule110WindowConsumer (false , false , false) = false

---- (1 MARK)
rule110 : Rule Bool Bool
rule110 =  (rule rule110WindowConsumer)
--
---- (1 MARK)
---- Define an initial state with: 90 dead cells, followed by 1 alive cell,
---- followed by anoter 90 dead cells
0⋯010⋯0 : List> Bool
0⋯010⋯0 = List>P._++_  (List>P.replicate 90 false) (List>P._++_ (true ,- []) (List>P.replicate 90 false))
--
---- (1 MARK)
---- Define an initial state with: 180 dead cells, followed by 1 alive cell
0⋯01 : List> Bool
0⋯01 = List>P._++_ (List>P.replicate 180 false) (true ,- [])


------------------------------------------------------------------------
-- Printing the results
------------------------------------------------------------------------

-- We need a bit of magic to actually get something out on the console

postulate
  toString : List> Char → String

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC List> = data [] ([] | (:)) #-}
{-# COMPILE GHC toString = T.pack #-}


display : List> Bool → String
display bs = toString (List>P.map (if_then '█' else ' ') bs)

record ⊤ : Set where
  constructor tt

{-# COMPILE GHC ⊤ = data () (()) #-}


{-# FOREIGN GHC import qualified Data.Text.IO as T #-}

postulate
  wait : ℕ → IO.Base.IO ⊤

{-# FOREIGN GHC import Control.Concurrent (threadDelay) #-}
{-# COMPILE GHC wait = threadDelay . fromIntegral #-}



------------------------------------------------------------------------
-- The function entrypoint


{-# NON_TERMINATING #-}
main : IO.Base.IO ⊤
main = do
  IO.Finite.putStrLn "Enter a binary rule (8 bits): "
  input <- getLine
  loop (0⋯010⋯0)

--main = loop (0⋯010⋯0) -- you can modify the initial state here

  where

  loop : List> Bool → IO.Base.IO _
  loop bs = do
    IO.Finite.putStrLn (display bs)
    wait 30000
    loop (step rule110 bs) -- you can modify the rule being used here


-- To run the project simply run `make cellular` in the `courseworks`
-- directory and then execute `./01-Cellular`


------------------------------------------------------------------------
-- Extend the project (15 MARKS)
------------------------------------------------------------------------

-- You are free to implement whatever you want. Try to put an emphasis
-- on elegant type & code. Here are some ideas:

-- * a command line interface with user-provided rules (cf. Wolfram codes)
-- * loop detection (if a state repeats itself, stop the program)
-- * treat the state of the cellular automaton as circular: the last cell
--   is considered to the left of the first one, and vice-versa.

{-{--}-}
