{-# OPTIONS --guardedness --erasure --rewriting #-}

------------------------------------------------------------------------
-- Coursework 2: Tiling (100 marks, 60% of course total)
--
-- The goal of this coursework is to write a Domain Specific Language
-- for manipulating images. We will use dependent types to keep track
-- of properties of the images, such as their width and height.
--
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Submission
--
-- Submit by pushing to your private coursework repository. It's
-- easiest to use the same repository as for Coursework 1, but we will
-- cope one way or another.
--
-- Deadline: Thursday 4 April at 5pm
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Life advice
--
-- It is not the case that the hard marks are all at the end of the
-- file, and the easy marks are at the beginning. Consequently, it
-- might be strategic to skip ahead if you get stuck.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Marks
--
-- Erasure                10 MARKS -- 10  -- 10
-- Fin                    30 MARKS -- 30  -- 40
-- Word8 and Pixel         6 MARKS -- 6   -- 46
-- Image                   4 MARKS -- 4   -- 50
-- Tile                   35 MARKS -- 35  -- 85
-- Extension              15 MARKS -- 90,180,270 degree rotation, CLI for selecting file to save, color inversion
--
-- TOTAL                 100 MARKS
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Imports and variable declarations
------------------------------------------------------------------------

-- If you need to import more things, that's okay, but it hopefully
-- should not be necessary (except for your extension, perhaps)

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_)
open import Data.Char.Base using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base as Maybe
  using (Maybe; nothing; just; fromMaybe; maybe)
open import Data.Nat as ℕ
  using (ℕ; zero; suc; _∸_; _+_; _*_; _<_; s≤s; z<s; s<s; _<?_; NonZero; _≡ᵇ_; _<ᵇ_)
import Data.Nat.Literals as ℕ; instance AgdaNumber = ℕ.number

-- /!\ Lots of good stuff in here! -----------
import Data.Nat.Properties as ℕₚ
import Data.Nat.DivMod as ℕₚ
----------------------------------------------

open import Data.String.Base using (String; fromList; _++_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)

open import Relation.Nullary using (Irrelevant)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; module ≡-Reasoning)
open import Agda.Builtin.Equality.Rewrite

open import Function.Base using (_$_; _∘_; _∋_; case_of_; flip)
open import Axiom.Extensionality.Propositional using (Extensionality)

variable
  A B C : Set

------------------------------------------------------------------------
-- Erasure (10 MARKS)
------------------------------------------------------------------------

-- For an efficient representation of Fin n, we will make use of a
-- recent feature of Agda: Runtime irrelevance. Arguments or record
-- fields marked with "@0" are guaranteed by Agda to have been erased
-- at runtime. Consequently, there are limitions on how such arguments
-- can be used.


-- (1 MARK)
-- Confirm that Agda lets you "unerase" when there is obviously at
-- most one constructor available.
unerase-≡ : ∀ {a} {A : Set a} {@0 x y : A} → @0 x ≡ y → x ≡ y
unerase-≡ refl = refl

unerase-⊥ : @0 ⊥ → ⊥
unerase-⊥ = \ ()

-- What happens if you try to unerase for example Bool?

-- `@0` is not a type former, but we can use a record wrapper to
-- effectively make it one.

record Erased (A : Set) : Set where
  constructor ∣_∣
  field
    @0 erased : A

-- (6 MARKS)
-- Which ones of the following are implementable? Either give an
-- implementation, or a short explanation for why it is not possible.

pure : A → Erased A
pure x =  ∣ x ∣

-- tries to reconstruct erased value A. Since erased values are not available at runtime, the function can't be implemented. return type depends on erased value.
-- more than one constructor could be available for type A
--extract : Erased A → A
--extract = {!!}

-- Tries to return P true or P false depending on b, but b is erased. At runtime, b will not be available, but P b depends on b, + Boolean has more than one constructor available
-- Therefore, the function is not implementable
--iftenelse : {P : Bool → Set} → (@0 b : Bool) → P true → P false → P b
--iftenelse {P} b t f = {!!}


erasedExtract : Erased (Erased A → A)
erasedExtract = ∣ (λ x → Erased.erased x) ∣


unerase-ℕ : Erased ℕ → ℕ
unerase-ℕ n = zero

-- since unerase-N performes type check and not reconstructs the N, not implementable.
--unerase-ℕ-correct : (n : ℕ) → unerase-ℕ (pure n) ≡ n
--unerase-ℕ-correct n = {!!}

module ErasedMonad where
-- (We put this in a module so we don't clash with _>>=_ for IO below)

  -- (2 MARKS)
  -- Show that Erased has the structure of a monad.
  -- Hint: the proofs of the laws should be pleasantly easy.
  _>>=_ : Erased A → (A → Erased B) → Erased B
  x >>= y = ∣ (Erased.erased (y (Erased.erased x))) ∣

  >>=-identityˡ : (a : A) → (f : A → Erased B) → pure a >>= f ≡ f a
  >>=-identityˡ = λ a f → refl

  >>=-identityʳ : (ea : Erased A) → ea >>= pure ≡ ea
  >>=-identityʳ = λ ea → refl

  >>=-assoc : (ea : Erased A) → (f : A → Erased B) → (g : B → Erased C)
            → (ea >>= f) >>= g ≡ (ea >>= λ x → f x >>= g)
  >>=-assoc = λ ea f g → refl

  -- (1 MARK)
  -- Use do-notation to implement the functorial action and the join for
  -- the monad.

  fmap : (A → B) → (Erased A → Erased B)
  fmap f ea = do
    ∣ (f (Erased.erased ea)) ∣

  squash : Erased (Erased A) → Erased A
  squash eea = do
    ∣ (Erased.erased (Erased.erased eea)) ∣

------------------------------------------------------------------------
-- Fin (30 MARKS)
------------------------------------------------------------------------

-- We will use Fin n to represent a position within an image that is
-- below the width or height n. For efficiency, we will use an unusual
-- representation of Fin n: rather than a data definition, we will
-- represent Fin n as natural numbers k such that k < n, but, and here
-- is the twist, we will ensure that the proof is not kept around at
-- runtime by marking it as runtime irrelevant.

record Fin (n : ℕ) : Set where
  constructor mkFin
  field
    value : ℕ
    @0 inBounds : value < n

-- (2 MARKS)
-- Implement the usual constructors for Fin.
fzero : ∀ {n} → Fin (suc n)
fzero = mkFin zero (s≤s ℕ.z≤n) 

fsuc : ∀ {n} → Fin n → Fin (suc n)
fsuc (mkFin value inBounds) = mkFin (suc value) (s≤s inBounds)

-- (1 MARK)
-- Show that fzero ≠ fsuc k for any k.
0≢1+n : ∀ {n} → (k : Fin n) → fzero ≡ fsuc k → ⊥
0≢1+n k ()


-- (1 MARK)
-- Show that fsuc is injective.
fsuc-injective : ∀ {n} → {k l : Fin n} → fsuc k ≡ fsuc l → k ≡ l
fsuc-injective refl = refl

-- (1 MARK)
-- Show that Fin 0 is the empty type, as expected.
¬Fin0 : ¬ (Fin 0)
¬Fin0 ()


cong-erased : ∀ {A B : Set} {@0 x y : A} (f : @0 A → B) → @0 (x ≡ y) → f x ≡ f y
cong-erased f refl = refl


-- (2 MARKS)
-- Show that two `Fin n` are equal as soon as their values are equal.
eqFin : ∀ {n} {k l : Fin n} → Fin.value k ≡ Fin.value l → k ≡ l
eqFin {n} {mkFin value inBounds} {mkFin value inBounds2} refl = cong-erased ((mkFin value)) (ℕₚ.≤-irrelevant inBounds inBounds2)



-- (2 MARKS)
-- Fin 1 is the unit type, as expected. Another way to phrase this is
-- to say that there is an element in Fin 1, and all elements in Fin 1
-- are the same.

Fin1-inhabited : Fin 1
Fin1-inhabited = mkFin zero (s≤s ℕ.z≤n)

Fin1-irrelevant : Irrelevant (Fin 1)
Fin1-irrelevant (mkFin zero (s≤s ℕ.z≤n)) (mkFin zero (s≤s ℕ.z≤n)) = refl

helper : ∀ {n} {k l : Fin n} → k ≡ l → Fin.value k ≡ Fin.value l
helper refl = refl



-- (2 MARKS)
_≟_ : ∀ {n} → (k l : Fin n) → Dec (k ≡ l)
mkFin value1 inBounds1 ≟ mkFin value2 inBounds2 with (value1 ℕ.≟ value2)
mkFin value1 inBounds1 ≟ mkFin value2 inBounds2 | yes eq = yes (eqFin eq)
mkFin value1 inBounds1 ≟ mkFin value2 inBounds2 | no neq = no λ x → neq (helper x)


¬s≤z : ∀ {m : ℕ} → ¬ (suc m ℕ.≤ zero)
¬s≤z ()

removeFromBothSides : ∀ {m n x}  → x  ℕ.≤ m + n  → (x ∸ m) ℕ.≤ n
removeFromBothSides {zero} {n} {x} x2 = x2
removeFromBothSides {suc m} {n} {zero} x2 = ℕ.z≤n
removeFromBothSides {suc m} {n} {suc x} x2 = removeFromBothSides (ℕ.s≤s⁻¹ x2)

equalize :  ∀ {m n x} → ¬ suc x ℕ.≤ m → suc x ∸ m ℕ.≤ n → suc (x ∸ m) ℕ.≤ n
equalize {zero} {n} {x} MlessthanX leq = leq
equalize {suc m} {n} {zero} MlessthanX leq with ℕₚ.≰⇒> MlessthanX
equalize {suc m} {zero} {zero} MlessthanX leq | res = Relation.Nullary.contradiction (ℕ.s≤s⁻¹ res) ¬s≤z
equalize {suc m} {suc n} {zero} MlessthanX leq | res = s≤s ℕ.z≤n
equalize {suc m} {n} {suc x} MlessthanX leq = equalize (λ q → MlessthanX (s≤s q)) leq

-- HARDER (4 MARKS)
-- Show that Fin distributes over +.
split : ∀ {m n} → Fin (m + n) → Fin m ⊎ Fin n
split {m} {n} (mkFin value inBounds) with value <? m
split {m} {n} (mkFin value inBounds) | yes proof = inj₁ (mkFin value proof) 
split {m} {n} (mkFin value inBounds) | no proof = inj₂ ( mkFin (value ∸ m) (equalize proof (removeFromBothSides inBounds)))


fjoin-helper1 : (m n value : ℕ) → suc value ℕ.≤ n → suc (m + value) ℕ.≤ m + n
fjoin-helper1 zero n value x = x
fjoin-helper1 (suc m) n value x = s≤s (fjoin-helper1 m n value x)

-- HARDER AGAIN (6 MARKS)
-- And show that in fact, split is an isomorphism.
fjoin : ∀ {m n} → Fin m ⊎ Fin n → Fin (m + n)
fjoin {m} {n} (inj₁ (mkFin value inBounds)) = mkFin value (ℕₚ.m≤n⇒m≤n+o n inBounds)
fjoin {m} {n} (inj₂ (mkFin value inBounds)) = mkFin (m + value) ( fjoin-helper1 m n value inBounds  )

shaveOff : {n m : ℕ} → (suc (suc n) ℕ.≤ suc m → ⊥) → ((suc n) ℕ.≤ m → ⊥)
shaveOff x x₁ = x (ℕ.s≤s x₁)

m+n-m=nBrackets : (m n : ℕ) → (suc n ℕ.≤ m → ⊥) →  m + (n ∸ m) ≡ n
m+n-m=nBrackets zero zero x = refl
m+n-m=nBrackets zero (suc n) x = refl
m+n-m=nBrackets (suc m) zero x = Relation.Nullary.contradiction (s≤s (ℕ.z≤n {m})) x
m+n-m=nBrackets (suc m) (suc n) x = cong suc (m+n-m=nBrackets m n (shaveOff x)) 

fjoin-split : ∀ {m} {n} → (k : Fin (m + n)) → fjoin (split {m} {n} k) ≡ k
fjoin-split {m} {n} (mkFin value inBounds) with value <? m
fjoin-split {m} {n} (mkFin value inBounds) | .true Relation.Nullary.because Relation.Nullary.ofʸ a = eqFin refl
fjoin-split {m} {n} (mkFin value inBounds) | .false Relation.Nullary.because Relation.Nullary.ofⁿ ¬a = eqFin (m+n-m=nBrackets m value ¬a) 


m+n-m=n : {m n : ℕ} → m + n ∸ m ≡ n
m+n-m=n {zero} {n} = refl
m+n-m=n {suc m} {n} = m+n-m=n {m} {n}

definitelyNotTrue : {m y : ℕ} → suc (m + y) ℕ.≤ m → ⊥
definitelyNotTrue {suc m} {n} less = definitelyNotTrue (ℕ.s≤s⁻¹ less)

split-fjoin : ∀ {m n} → (x : Fin m ⊎ Fin n) → split (fjoin x) ≡ x
split-fjoin {m} {n} (inj₁ x) with Fin.value x <? m
split-fjoin {m} {n} (inj₁ x) | .true Relation.Nullary.because Relation.Nullary.ofʸ a = cong inj₁ (eqFin refl)
split-fjoin {m} {n} (inj₁ (mkFin value inBounds)) | .false Relation.Nullary.because Relation.Nullary.ofⁿ ¬a = unerase-≡ (Relation.Nullary.contradiction inBounds ¬a)
split-fjoin {m} {n} (inj₂ y) with (m + Fin.value y) <? m
split-fjoin {m} {n} (inj₂ y) | .true Relation.Nullary.because Relation.Nullary.ofʸ a = Relation.Nullary.contradiction a definitelyNotTrue
split-fjoin {m} {n} (inj₂ y) | .false Relation.Nullary.because Relation.Nullary.ofⁿ ¬a = cong inj₂ (eqFin (m+n-m=n {m} {Fin.value y}) )


-- (2 MARKS)
-- Define the function which sends 0 ↦ m-1, 1 ↦ m-2, ..., m-1 ↦ 0.

n≤n : ∀ w → w ℕ.≤ w
n≤n zero = ℕ.z≤n
n≤n (suc w) = s≤s (n≤n w)


complement : ∀ {m} → Fin m → Fin m
complement {suc m} (mkFin value inBounds) = mkFin (m  ∸ value) (ℕ.s≤s (ℕₚ.m∸n≤m m value))


inverseLemma : ∀ {m} (k : Fin (suc m)) → (Fin.value (complement (complement k))) ≡ m ∸ (m ∸ Fin.value k)
inverseLemma {m} (mkFin zero inBounds) = refl
inverseLemma {m} (mkFin (suc value) inBounds) = refl


-- (3 MARKS)
-- Show that complement is its own inverse.
complement-inverse : ∀ {m} → (k : Fin m) → complement (complement k) ≡ k
complement-inverse {suc m} (mkFin value inBounds) = eqFin (Relation.Binary.PropositionalEquality.trans (inverseLemma ((mkFin value inBounds)))
    (unerase-≡ (ℕₚ.m∸[m∸n]≡n (ℕ.s≤s⁻¹ inBounds))))

-- (1 MARK)
-- Use remainders of natural numbers and its properties to implement
-- remainders targetting Fin.
_%_ : ℕ → (i : ℕ) → .{{NonZero i}} → Fin i
k % i with ℕₚ.m%n<n k i
k % i | x with k ℕ.% i
k % i | x | mod = mkFin mod x


-- (1 MARK)
-- Show that `_% i` is not injective for your choice of i.
%-not-injective : let i = 5
                      k = 2
                      l = 7
                      eq : (k % i) ≡ (l % i)
                      eq = refl
                   in k ≡ l → ⊥
%-not-injective = \ ()


-- Using k % i, we can now allow ourselves to use decimal notation
-- when writing a Fin.

open import Agda.Builtin.FromNat
instance
  FinNumber : ∀ {n} → .{{NonZero n}} → Number (Fin n)
  FinNumber .Number.Constraint k = ⊤
  FinNumber {n} .Number.fromNat k = k % n

private
  -- Try evaluating these:

  testFin : Fin 128
  testFin = 5

  testFin' : Fin 2
  testFin' = 130

-- (2 MARKS)
-- Construct division for Fin, with a precise type.

transR : {a b c : ℕ} → a ≡ b → c ℕ.≤ a → c ℕ.≤ b
transR refl x = x

transL : {a b c : ℕ} → a ≡ b → b ℕ.≤ c → a ℕ.≤ c
transL refl x = x

finSubst : ∀ {m n} → m ≡ n → Fin m → Fin n
finSubst refl x₁ = x₁

quotHelp : ∀ i → i * zero ≡ zero
quotHelp zero = refl
quotHelp (suc n) = quotHelp n



quot : ∀ {w} i → .{{NonZero i}} → Fin (i * w) → Fin w
quot {w = zero} i (mkFin value inBounds) = Relation.Nullary.contradiction ( (finSubst (quotHelp i) (mkFin value inBounds))) ¬Fin0
quot {w = suc w} i (mkFin value inBounds) = mkFin ((value ℕₚ./ i) ) ( ℕₚ.m<n*o⇒m/o<n  (transR (ℕₚ.*-comm i ((suc w))) inBounds)   )


------------------------------------------------------------------------
-- Word8 and Pixel (6 MARKS)
------------------------------------------------------------------------

-- We will represent pixels as RGB values of Haskell 8-bit words,
-- which we represent in Agda as natural numbers. First we get a bunch
-- of Haskell integration out of the way.

postulate
  Word8 : Set
  fromℕ' : ℕ → Word8
  toℕ : Word8 → ℕ

-- NOTE: Do not use fromℕ', because it does not compute in Agda (only
-- at runtime). Instead use fromℕ (which computes thanks to the
-- rewrite rule below).

abstract
  fromℕ : (n : ℕ) → (@0 p : n < 256) → Word8
  fromℕ n _ = fromℕ' n

postulate
  toℕ-fromℕ : (n : ℕ)(p : n < 256) → toℕ (fromℕ n p) ≡ n
  toℕ-fromℕ' : ∀ n → toℕ (fromℕ' n) ≡ n
  
  
{-# REWRITE toℕ-fromℕ #-}
{-# REWRITE toℕ-fromℕ' #-}

{-# FOREIGN GHC import Data.Word #-}
{-# COMPILE GHC Word8 = type Word8 #-}
{-# COMPILE GHC fromℕ' = fromInteger #-}
{-# COMPILE GHC toℕ = toInteger #-}

instance
  Word8Number : Number Word8
  Word8Number .Number.Constraint n = ⊤
  Word8Number .Number.fromNat n = fromℕ (n ℕ.% 256) (ℕₚ.m%n<n n 256)

-- Here is our type of pixels.

record Pixel : Set where
  constructor mkPixel
  field
    red : Word8
    green : Word8
    blue : Word8

{-# FOREIGN GHC import Codec.Picture #-}
{-# COMPILE GHC Pixel = data PixelRGB8 (PixelRGB8) #-}

-- And here are some examples of pixels:
fullred fullgreen fullblue navy azur cyan skyblue yellow black white purple parma pastelGreen : Pixel
fullred = mkPixel 255 0 0
fullgreen = mkPixel 0 255 0
fullblue = mkPixel 0 0 255
navy = mkPixel 16 24 107
azur = mkPixel 16 82 214
cyan = mkPixel 157 247 247
skyblue = mkPixel 74 165 239
yellow = mkPixel 255 255 51
black = mkPixel 0 0 0
white = mkPixel 255 255 255
purple = mkPixel 102 0 102
parma = mkPixel 255 153 204
pastelGreen = mkPixel 232 249 233

-- (0 MARKS)
-- Fill in your favourite colour as a pixel here.
myFavouriteColour : Pixel
myFavouriteColour = mkPixel 255 255 255

-- (4 MARKS)
-- For debugging, write a function for displaying an ASCII
-- representation of a pixel. This is the specification:
--
-- If a pixel is black, return '#'.
-- If a pixel is only red, green or blue, you should return an
-- uppercase 'R', 'G' or 'B' respectively.
-- Otherwise return
--   a lowercase 'r' if the pixel is red more than anything else,
--   a lowercase 'g' if it is green  more than anything else,
--   a lowercase 'b' if it is blue  more than anything else,
--   a lowercase 't' if it is most green and blue ("turquoise"),
--   a lowercase 'y' if it is most red and green ("yellow"),
--   a lowercase 'p' if it is most red and blue ("purple"), and
--   a '.' if all colours have the same intensity.



-- _∧_; _∨

showPixel : Pixel → Char
showPixel (mkPixel red green blue) with (toℕ blue ≡ᵇ 0) ∧ (toℕ green ≡ᵇ 0) ∧ (toℕ red ≡ᵇ 0)                 -- all
showPixel (mkPixel red green blue) | true = '#'
showPixel (mkPixel red green blue) | false with (toℕ green ≡ᵇ 0) ∧ (toℕ red ≡ᵇ 0)                         -- only Blue
showPixel (mkPixel red green blue) | _ | true = 'B'
showPixel (mkPixel red green blue) | _ | _ with (toℕ blue ≡ᵇ 0) ∧ (toℕ red ≡ᵇ 0)                          -- green
showPixel (mkPixel red green blue) | _ | _ | true = 'G'
showPixel (mkPixel red green blue) | _ | _ | _ with (toℕ blue ≡ᵇ 0) ∧ (toℕ green ≡ᵇ 0)                    -- red
showPixel (mkPixel red green blue) | _ | _ | _ | true = 'R'
showPixel (mkPixel red green blue) | _ | _ | _ | _ with ((toℕ green) ≡ᵇ (toℕ blue)) ∧ ((toℕ red) <ᵇ (toℕ green))     -- green blue
showPixel (mkPixel red green blue) | _ | _ | _ | _ | true = 't'
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _  with (toℕ green ≡ᵇ toℕ red) ∧ ((toℕ blue) <ᵇ (toℕ green))    -- green red
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _ | true = 'y'
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _ | _ with (toℕ blue ≡ᵇ toℕ red) ∧ ((toℕ green) <ᵇ (toℕ blue))   -- blue red
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _ | _ | true = 'p'
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _ | _ | _ with (toℕ red ≡ᵇ toℕ green) ∧ (toℕ green ≡ᵇ toℕ red)   -- all
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _ | _ | _ | true = '.'
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _ | _ | _ | _ with (toℕ green  <ᵇ toℕ red) ∧ ((toℕ blue) <ᵇ (toℕ red))         -- red
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _ | _ | _ | _ | true = 'r'
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _ | _ | _ | _ | _ with (toℕ blue  <ᵇ toℕ green) ∧ ((toℕ red) <ᵇ (toℕ green))   -- green
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _ | _ | _ | _ | _ | true = 'g'
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ with (toℕ green <ᵇ toℕ blue) ∧ ((toℕ red) <ᵇ (toℕ blue))   -- blue 
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | true = 'b'
showPixel (mkPixel red green blue) | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ = 'N'



-- Here is a test case to make sure you got it right:
_ : Data.List.Base.map showPixel
                       (fullred ∷ fullgreen ∷ fullblue ∷ navy ∷ azur ∷ cyan ∷ skyblue ∷ yellow ∷ black ∷ white ∷ purple ∷ parma ∷ pastelGreen ∷ [])
  ≡ ('R' ∷ 'G' ∷ 'B' ∷ 'b' ∷ 'b' ∷ 't' ∷ 'b' ∷ 'y' ∷ '#' ∷ '.' ∷ 'p' ∷ 'r' ∷ 'g' ∷ [])
_ = refl

-- (2 MARKS)
-- Is showPixel injective? Either prove it, or produce a
-- counterexample. Comment out the one that does not apply.

--showPixel-injective : (p p' : Pixel) → showPixel p ≡ showPixel p' → p ≡ p'
--showPixel-injective p p' x = {!!}

proofHelp : {a b : Pixel} ->  a ≡ b -> toℕ (Pixel.red a) ≡ toℕ (Pixel.red b)
proofHelp refl = refl

showPixel-not-injective : let p  = mkPixel 0 1 2
                              p' = mkPixel 1 0 2
                              eq : showPixel p ≡ showPixel p'
                              eq = refl
                           in p ≡ p' → ⊥
showPixel-not-injective x with (proofHelp x)
... | ()

-- Again: prove one, comment out the other. Do not try to prove both.

------------------------------------------------------------------------
-- Image (4 MARKS)
------------------------------------------------------------------------

-- We can represent an image as an assignment of a pixel for each
-- coordinate.

record Image (m n : ℕ) : Set where
  constructor mkImage
  field runImage : Fin m → Fin n → Pixel
open Image

-- (1 MARK)
-- Build some colourful squares.

redSquare : Image 8 8
redSquare = mkImage (λ x y → mkPixel 8 0 0)

blueSquare : Image 8 8
blueSquare = mkImage (λ x y → mkPixel 0 0 8)

greenSquare : Image 8 8
greenSquare = mkImage (λ x y → mkPixel 0 8 0)


row : (w h x : ℕ) → (@0 px : x < w) → (y : Fin h) → Image w h → String
row w h zero px y image = Data.String.Base.fromChar (showPixel (runImage image (mkFin (zero) px) y))
row w h (suc x) px y image = row w h x (ℕ.s≤s⁻¹ (ℕₚ.m≤n⇒m≤1+n px)) y image ++ Data.String.Base.fromChar (showPixel (runImage image (mkFin (suc x) px) y))

genImage : (w h x y : ℕ) → (@0 px : x < w) → (@0 py : y < h) → Image w h → String
genImage w h x zero px py img = row w h x  px  (mkFin zero py) img
genImage w h x (suc y) px py img = (genImage w h x y px ((ℕ.s≤s⁻¹ (ℕₚ.m≤n⇒m≤1+n py))) (img)  ++ "\n" ++ ( row ( w) ( h) x px (mkFin (suc y) py) img )) 


-- (3 MARKS)
-- Use showPixel to show a whole image.
show : {w h : ℕ} → Image w h → String
show {zero} {h} (mkImage runImage₁) = ""
show {suc w} {zero} (mkImage runImage₁) = ""
show {suc w} {suc h} (mkImage runImage₁) = genImage (suc w) (suc h) w h (n≤n (suc w)) (n≤n (suc h)) (mkImage (λ x x₁ → runImage₁ x x₁ ))


-- Hint: You can get Agda to print using your show function on a term
--  by doing C-u C-u C-c C-n; easiest is to write a hole, eg
--
-- test = {! !}
--
--  and then do C-u C-u C-c C-n in the hole.
--  (The C-u C-u in this case means "use the `show` function in
--  scope".)

-- With a bit more boilerplate, we can call out to the JuicyPixels
-- library in Haskell to save our images in PNG format when running
-- the compiled code:

open import Level using (0ℓ)
open import IO.Base using (IO; lift!; lift; Main; run; _>>=_; _>>_)
open import IO.Finite
import IO.Primitive as Prim

postulate
  primSavePngImage : String → (m n : ℕ) → (ℕ → ℕ → Pixel) → Prim.IO {0ℓ} ⊤

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC primSavePngImage = \ fp m n fun ->
      savePngImage (T.unpack fp)
    $ ImageRGB8
    $ generateImage
      (\ x y -> fun (fromIntegral x) (fromIntegral y))
      (fromInteger m) (fromInteger n)
#-}

savePngImage : {m n : ℕ} → String → Image m n → IO {0ℓ} _
savePngImage {m} {n} fp (mkImage fun)
  = lift! (lift (primSavePngImage fp m n fun′)) where

  cast : (m n : ℕ) → Maybe (Fin m)
  cast 0 _ = nothing
  cast (suc m) zero = just fzero
  cast (suc m) (suc n) = Maybe.map fsuc (cast m n)

  fun′ : (ℕ → ℕ → Pixel)
  fun′ k l with cast m k | cast n l
  ... | just x | just y = fun x y
  ... | _ | _ = mkPixel (fromℕ 0 (s≤s ℕ.z≤n)) (fromℕ 0 (s≤s ℕ.z≤n)) (fromℕ 0 (s≤s ℕ.z≤n))

------------------------------------------------------------------------
-- Tile (35 MARKS)
------------------------------------------------------------------------

-- An image is a 2D array of pixels. We can abstract away from pixels
-- to arbitrary data in some set A:

record Tile (width height : ℕ) (A : Set) : Set where
  constructor mkTile
  field runTile : Fin width → Fin height → A
open Tile

variable
  w w₁ w₂ : ℕ
  h h₁ h₂ : ℕ

-- (1 MARK)
-- Construct a way to change the data stored in a tile.
map : (A → B) → Tile w h A → Tile w h B
Tile.runTile (map f (mkTile runTile)) fin1 fin2 = f (runTile fin1 fin2)


-- (2 MARKS)
-- State and prove that map preserves identities and composition
-- (pointwise).


map-id : (t : Tile w h A) → map (λ x → x) t ≡ t
map-id {w} {h} {A} (mkTile runTile₁) = cong mkTile refl


map-comp : (g : B → C)(f : A → B) → (t : Tile w h A) → map (g ∘ f) t ≡ map g (map f t)
map-comp {B} {C} {A} {w} {h} g f t = refl

-- (1 MARK)
-- Do the same combining data from two tiles, position-wise.
zipWith : (A → B → C) → Tile w h A → Tile w h B → Tile w h C
runTile (zipWith x x₁ x₂) x₃ x₄ with (runTile x₁  x₃ x₄) | (runTile x₂ x₃ x₄)
runTile (zipWith f x₁ x₂) x₃ x₄ | A | B = f A B

-- (1 MARK)
-- Use zipWith to define a combinator for putting one tile in front of
-- the other, where `nothing` signifies holes in the front tile,
-- seeing through to the back tile.

func : (Maybe A) → A → A
func (just x) x₁ = x
func nothing x₁ = x₁ 

_◂_ : Tile w h (Maybe A) → Tile w h A → Tile w h A
tileMaybe ◂ tile = zipWith func tileMaybe tile

-- (1 MARK)
-- Show that you can flip a tile along its axis.
transpose : Tile w h A → Tile h w A
runTile (transpose x) x₁ x₂ = runTile x x₂ x₁

-- (1 MARK)
-- Show that you can fill an arbitrary tile with a fixed colour.
fill : (w h : ℕ) → A → Tile w h A
fill w zero x = mkTile (λ x₁ x₂ → Relation.Nullary.contradiction x₂ ¬Fin0)
fill zero (suc h) x = mkTile (λ x₁ x₂ → Relation.Nullary.contradiction x₁ ¬Fin0)
fill (suc w) (suc h) x = mkTile (λ x₁ x₂ → x)

equality : (h₁ : ℕ) →  (h₁ * zero) ≡ 0
equality zero = refl
equality (suc h₁) = equality h₁

elim : ∀ (h₁ : ℕ) →  Fin (h₁ * zero) -> Fin 0
elim h₁ (mkFin value inBounds) = finSubst (equality h₁) ((mkFin value inBounds))

swap : (a b : ℕ) →  Fin (a * b)  →  Fin (b * a)
swap a b x = finSubst (ℕₚ.*-comm a b) x

-- HARD (4 MARKS)
-- Show that you can merge together two layers of tiles into one layer.
join : Tile w₁ h₁ (Tile w₂ h₂ A) → Tile (w₁ * w₂) (h₁ * h₂) A
join {w₁ = zero} {h₁ = h₁} {w₂ = w₂} {h₂ = h₂} x = mkTile (λ x₁ x₂ → Relation.Nullary.contradiction x₁ ¬Fin0)
join {w₁ = suc w₁} {h₁ = zero} {w₂ = w₂} {h₂ = h₂} x = mkTile (λ x₁ x₂ → Relation.Nullary.contradiction x₂ ¬Fin0)
join {w₁ = suc w₁} {h₁ = suc h₁} {w₂ = zero} {h₂ = h₂} x = mkTile (λ x₁ x₂ → Relation.Nullary.contradiction (elim w₁ x₁) ¬Fin0  )
join {w₁ = suc w₁} {h₁ = suc h₁} {w₂ = suc w₂} {h₂ = zero} x = mkTile (λ x₁ x₂ → Relation.Nullary.contradiction (elim h₁ x₂) ¬Fin0)
join {w₁ = suc w₁} {h₁ = suc h₁} {w₂ = suc w₂} {h₂ = suc h₂} x = mkTile (λ x₁ x₂ → ultimateAssistant x₁ x₂ x)
  where
  ultimateAssistant : Fin ((suc w₁) * (suc w₂)) → Fin((suc h₁) * (suc h₂)) → Tile (suc w₁) (suc h₁) (Tile (suc w₂) (suc h₂) A) → A
  ultimateAssistant x x₁ tile with (quot (suc w₂) (swap (suc w₁) (suc w₂) x)) | (quot (suc h₂) (swap (suc h₁) (suc h₂) x₁)) |  (Fin.value x) % (suc w₂) | Fin.value x₁ % (suc h₂)
  ultimateAssistant x x₁ tile | W1 | H1 | W2 | H2 = Tile.runTile (Tile.runTile tile W1 H1) W2 H2

  
-- (1 MARK)
-- Images are basically the same things as tiles of pixels.
fromImage : Image w h → Tile w h Pixel
runTile (fromImage (mkImage runImage₁)) x₁ x₂ = runImage₁ x₁ x₂

toImage : Tile w h Pixel → Image w h
runImage (toImage x) x₁ x₂ = runTile x x₁ x₂



-- (2 MARKS)
-- Given a coordinate x y and a tile of pixels, we can
-- create an image focused at that coordinate (wrapping around if the
-- coordinate is too large). This gives us the basics of tiling!
focusAt : ∀ {i j} → .{{NonZero i}} → .{{NonZero j}} →
          ℕ → ℕ → Tile i j Pixel → Image w h
runImage (focusAt {i = i} {j = j} x y tile) finw finh = Tile.runTile tile ((Fin.value finw + i ∸ (Fin.value (x % i))) % i) ((Fin.value finh + j ∸ (Fin.value (y % i))) % j) 

-- (1 MARK)
-- In particular, use focusAt to convert from tiles of pixels to images
-- in a "wrapping around" way
wrapTile : ∀ {i j} → Tile (suc i) (suc j) Pixel → Image w h
wrapTile {i = i} {j = j} x = (focusAt 0 0 x)


-- (1 MARK)
-- Given a coordinate in a tile, we can also change the value at that
-- particular coordinate.
setPixel : Fin w → Fin h → A → Tile w h A → Tile w h A
setPixel (mkFin value inBounds) (mkFin value₁ inBounds₁) A (mkTile runTile₁) = mkTile (λ x x₁ → Data.Bool.Base.if (value ≡ᵇ (Fin.value x)) ∧ (value₁ ≡ᵇ (Fin.value x₁)) then A else (runTile₁ x x₁))

-- Here is a test case you can try to show (C-u C-u C-c C-n almostRedSquare):
almostRedSquare : Image 8 8
almostRedSquare = toImage (setPixel 1 3 fullblue (fromImage redSquare))

-- HARD, BECAUSE AGDA CAN BE CLUNKY (4 MARKS)
-- Show that, assuming function extensionality, setting the same pixel
-- twice overwrites the first attempt.

proofGod : ∀ {b : Bool} (a a' c : A) {x : Fin w} {x₁ : Fin h} (t : Tile w h A) -> (Data.Bool.Base.if b then a else (Data.Bool.Base.if b then a' else Tile.runTile t x x₁)) ≡ (Data.Bool.Base.if b then a else Tile.runTile t x x₁)
proofGod {A} {w} {h} {false} a a' c {x} {x₁} t = refl
proofGod {A} {w} {h} {true} a a' c {x} {x₁} t = refl


setPixel-setPixel : (ext : Extensionality 0ℓ 0ℓ)
                  → (x : Fin w) → (y : Fin h) → (a a' : A) → (t : Tile w h A)
                  → setPixel x y a (setPixel x y a' t) ≡ setPixel x y a t
setPixel-setPixel {w} {h} {A} ext (mkFin value inBounds) (mkFin value₁ inBounds₁) a a' t with (setPixel (mkFin value inBounds) (mkFin value₁ inBounds₁) a' t)
setPixel-setPixel {w} {h} {A} ext (mkFin value inBounds) (mkFin value₁ inBounds₁) a a' t | tile1 = cong mkTile (ext (λ x → ext (λ x₁ → proofGod a a' (Tile.runTile t x x₁) t)))


-- (2 MARKS)
-- Show that we can scale a tile both horizontally and vertically.
hScale : ∀ i → Tile w h A → Tile (i * w) h A
runTile (hScale (suc i) x) x₁ x₂ with quot (suc i) x₁
runTile (hScale (suc i) x) x₁ x₂ | res = Tile.runTile x res  x₂  

vScale : ∀ i → Tile w h A → Tile w (i * h) A
runTile (vScale (suc i) x) x₁ x₂ with quot (suc i) x₂
runTile (vScale (suc i) x) x₁ x₂ | res = Tile.runTile x x₁ res

-- (1 MARK)
-- Use hScale and vScale to scale in both dimensions at the same time.
scale : ∀ i → Tile w h A → Tile (i * w) (i * h) A
scale i tile = vScale i (hScale i tile)

-- Test case:
scaledSquare : Image 16 16
scaledSquare = toImage (scale 2 (fromImage greenSquare))

-- (3 MARKS)
-- Show how to put one tile above another, or one to the right of another.
infixr 2 _─_
infixr 3 _∥_


_─_ : Tile w h₁ A → Tile w h₂ A → Tile w (h₁ + h₂) A
runTile (mkTile runTile₁ ─ mkTile runTile₂) fw f12 with split f12 
runTile (mkTile runTile₁ ─ mkTile runTile₂) fw f12 | inj₁ left = runTile₁ fw left
runTile (mkTile runTile₁ ─ mkTile runTile₂) fw f12 | inj₂ right = runTile₂ fw right

redGreenSquare : Image 8 16
redGreenSquare = toImage (fromImage redSquare ─ fromImage greenSquare)

_∥_ : Tile w₁ h A → Tile w₂ h A → Tile (w₁ + w₂) h A
runTile (mkTile runTile₁ ∥ mkTile runTile₂) x x₁ with split x
runTile (mkTile runTile₁ ∥ mkTile runTile₂) x x₁ | inj₁ x₂ = runTile₁ x₂ x₁
runTile (mkTile runTile₁ ∥ mkTile runTile₂) x x₁ | inj₂ y = runTile₂ y x₁

greenBlueSquare : Image 16 8
greenBlueSquare = toImage (fromImage greenSquare ∥ fromImage blueSquare)

gbrgSquare : Image 16 16
gbrgSquare = toImage $ (fromImage greenSquare ∥ fromImage blueSquare) ─ (fromImage redSquare ∥ fromImage greenSquare)


-- (2 MARKS)
-- Construct mirroring horizontally and vertically.
hMirror : Tile w h A → Tile w h A
runTile (hMirror (mkTile runTile₁)) = λ x x₁ → runTile₁ (complement x)  x₁

vMirror : Tile w h A → Tile w h A
runTile (vMirror (mkTile runTile₁)) = λ x x₁ → runTile₁ x (complement x₁) 

grbgSquare : Image 16 16
grbgSquare = toImage $ hMirror $ vMirror $ fromImage $ gbrgSquare

-- (2 MARKS)
-- Use ─ and ∥ to make an i pixels wide border around a given tile.

border : (i : ℕ) → A → Tile w h A → Tile (i + (w + i)) (i + (h + i)) A
border {w = w} {h = h} i a tile with (fill w i a) | (fill i (h + i) a) | (fill (w + i) i a) | (fill i (i + (h + i)) a)
border {w = w} {h = h} i a tile | x1 | x2 | x3 | x4 =  x4 ∥(x3 ─ ((tile ─ x1) ∥ x2)) 


-- _─_ _∥_

borderedSquare : Image 20 20
borderedSquare = toImage $ border 2 black $ fromImage gbrgSquare

-- (2 MARKS)
-- Take the top left quadrant and produce a full rectangle by
-- symmetries: e.g.  if the tile is the image '⬀', quadrants should
-- produce the image
--
--    ⬀⬁
--    ⬂⬃
--

-- the equality is true only when w >= h
-- it allows to subtract h from both sides
quadrantsGigaChad : (w h : ℕ) → ((suc w ℕ.≤ h) → ⊥) → suc (w ∸ h) ≡ (suc w) ∸ h
quadrantsGigaChad zero zero x = refl
quadrantsGigaChad zero (suc h) x = Relation.Nullary.contradiction (s≤s ℕ.z≤n) x
quadrantsGigaChad (suc w) zero x = refl
quadrantsGigaChad (suc w) (suc h) x = quadrantsGigaChad w h λ x₁ → x (ℕ.s≤s x₁)

generateFin : (a : ℕ) (t : Fin (a + a)) → ¬ suc (Fin.value t) ℕ.≤ a  → Fin a
generateFin a (mkFin value inBounds) ¬a = mkFin (value ∸ a) ((transL (quadrantsGigaChad value a ¬a) (transR (ℕₚ.m+n∸n≡m a a) (ℕₚ.∸-monoˡ-≤ a inBounds))))

quadrants : Tile w h A → Tile (w + w) (h + h) A
runTile (quadrants {w = w} {h = h} x) = λ x₁ x₂ → quadrantsHelper x₁ x₂ x
  where
  quadrantsHelper : Fin (w + w) → Fin (h + h) → Tile w h A → A
  quadrantsHelper  (mkFin value inBounds) (mkFin value1 inBounds1) tile with suc value ℕₚ.≤? w | suc value1 ℕₚ.≤? h
  ... | no ¬a | no ¬a₁ = runTile tile  (generateFin w ((mkFin value inBounds)) ¬a) (generateFin h ((mkFin value1 inBounds1)) ¬a₁)
  ... | no ¬a | yes a = runTile tile (generateFin w ((mkFin value inBounds)) ¬a)  (mkFin value1 a)
  ... | yes a | no ¬a = runTile tile ((mkFin value a)) (generateFin h ((mkFin value1 inBounds1)) ¬a)  
  ... | yes a | yes a₁ = runTile tile (mkFin value a) (mkFin value1 a₁)


quadborderedSquare : Image 40 40
quadborderedSquare = toImage $ quadrants $ fromImage borderedSquare

fin : Fin 10
fin = mkFin zero (s≤s ℕ.z≤n)

-- (3 MARKS)
-- Using the combinators you have written, create your own image!
-- Try to make it look nice.
-- Packman, used fill, border, ∥, setPixel
myImage : Image 300 180 -- 
myImage = toImage (scale 10 (setPixel (mkFin 7 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))(mkFin 8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))) yellow   (setPixel (mkFin 6 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))(mkFin 8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))) yellow    (setPixel (mkFin 13 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))))))(mkFin 8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))) yellow   (setPixel (mkFin 12 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))))))(mkFin 8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))) yellow  (setPixel (mkFin 7 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))(mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))) yellow   (setPixel (mkFin 6 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))(mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))) yellow    (setPixel (mkFin 13 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))))))(mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))) yellow   (setPixel (mkFin 12 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))))))(mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))) yellow  (border 3 fullblue ((fill 14 12 fullblue) ∥ (setPixel (mkFin 3 (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))(mkFin 2 (s≤s (s≤s (s≤s ℕ.z≤n)))) black     (setPixel (mkFin 7 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))(mkFin 0 (s≤s ℕ.z≤n)) fullblue    (setPixel (mkFin 6 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))(mkFin 0 (s≤s ℕ.z≤n)) fullblue  (setPixel (mkFin 6 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))(mkFin 11 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))))) fullblue   (setPixel (mkFin 7 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))(mkFin 11 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))))) fullblue   (setPixel (mkFin 8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))(mkFin 11 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))))) fullblue     (setPixel (mkFin 8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))(mkFin 10 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))) fullblue  (setPixel (mkFin 8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))(mkFin 1 (s≤s (s≤s ℕ.z≤n))) fullblue     (setPixel (mkFin 8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))(mkFin 0 (s≤s ℕ.z≤n)) fullblue    (setPixel (mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))(mkFin 0 (s≤s ℕ.z≤n)) fullblue    (setPixel (mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))(mkFin 1 (s≤s (s≤s ℕ.z≤n))) fullblue    (setPixel (mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))(mkFin 2 (s≤s (s≤s (s≤s ℕ.z≤n)))) fullblue     (setPixel (mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))(mkFin 3 (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))) fullblue      (setPixel (mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))(mkFin 8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))) fullblue     (setPixel (mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))(mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))) fullblue     (setPixel (mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))(mkFin 10 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))) fullblue         (setPixel (mkFin 9 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))(mkFin 11 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))))) fullblue         (setPixel (mkFin 2 (s≤s (s≤s (s≤s ℕ.z≤n))))(mkFin 11 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))))) fullblue       (setPixel (mkFin 1 (s≤s (s≤s ℕ.z≤n)))(mkFin 11 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))))) fullblue        (setPixel (mkFin 0 (s≤s ℕ.z≤n))(mkFin 11 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))))))) fullblue       (setPixel (mkFin 0 (s≤s ℕ.z≤n))(mkFin 10 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))))) fullblue      (setPixel (mkFin 0 (s≤s ℕ.z≤n))(mkFin 8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))))) fullblue        (setPixel (mkFin 1 (s≤s (s≤s ℕ.z≤n)))(mkFin 7 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))) fullblue        (setPixel (mkFin 0 (s≤s ℕ.z≤n))(mkFin 7 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))))) fullblue      (setPixel (mkFin 2 (s≤s (s≤s (s≤s ℕ.z≤n))))(mkFin 6 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))) fullblue       (setPixel (mkFin 1 (s≤s (s≤s ℕ.z≤n)))(mkFin 6 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))) fullblue      (setPixel (mkFin 0 (s≤s ℕ.z≤n))(mkFin 6 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))))) fullblue     (setPixel (mkFin 2 (s≤s (s≤s (s≤s ℕ.z≤n))) )(mkFin 5 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))) fullblue      (setPixel (mkFin 1 (s≤s (s≤s ℕ.z≤n)) )(mkFin 5 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))) fullblue     (setPixel (mkFin 0 (s≤s ℕ.z≤n) )(mkFin 5 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))))) fullblue     (setPixel (mkFin 1 (s≤s (s≤s ℕ.z≤n)) )(mkFin 4 (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))) fullblue      (setPixel (mkFin 0 (s≤s ℕ.z≤n) )(mkFin 4 (s≤s (s≤s (s≤s (s≤s (s≤s ℕ.z≤n)))))) fullblue    (setPixel (mkFin 0 (s≤s ℕ.z≤n) )(mkFin 3 (s≤s (s≤s (s≤s (s≤s ℕ.z≤n))))) fullblue    (setPixel (mkFin 0 (s≤s ℕ.z≤n) )(mkFin 1 (s≤s (s≤s ℕ.z≤n))) fullblue   (setPixel (mkFin 2 (s≤s (s≤s (s≤s ℕ.z≤n))) )(mkFin 0 (s≤s ℕ.z≤n)) fullblue  (setPixel (mkFin 1 (s≤s (s≤s ℕ.z≤n)) )(mkFin 0 (s≤s ℕ.z≤n)) fullblue (setPixel (mkFin 0 (s≤s ℕ.z≤n) )(mkFin 0 (s≤s ℕ.z≤n)) fullblue (fill 10 12 yellow)))))))))))))))))))))))))))))))))))))))))))))))))








-- Here is a more complicated tile using most of the things you have produced so far.
flower : Tile 30 30 Pixel
flower = border 3 white
       $ quadrants
       $ square ◂ transpose (map (fromMaybe white) square)

  where

  square : Tile 12 12 (Maybe Pixel)
  square =
      fill 8 1 nothing ∥ fill 2 1 (just navy) ∥ fill 2 1 nothing
    ─ fill 6 1 nothing ∥ fill 2 1 (just navy) ∥ fill 2 1 (just azur) ∥ fill 1 1 (just navy) ∥ fill 1 1 nothing
    ─ fill 5 3 nothing ∥ fill 1 3 (just navy)
         ∥ (fill 1 1 (just azur) ∥ fill 1 1 (just cyan) ∥ fill 2 1 (just azur) ∥ fill 1 1 (just navy) ∥ fill 1 1 nothing
           ─ (fill 2 2 (just azur) ∥ ((fill 1 1 (just cyan) ∥ fill 2 1 (just skyblue))
                                    ─ (fill 1 1 nothing ∥ fill 1 1 (just cyan) ∥ fill 1 1 (just skyblue))))
              ∥ fill 1 2 (just navy))
    ─ fill 6 2 nothing ∥ fill 1 2 (just navy) ∥ fill 1 2 (just skyblue)
                       ∥ fill 1 2 (just cyan) ∥ fill 1 2 nothing ∥ fill 1 2 (just cyan)
                       ∥ fill 1 2 (just navy)
    ─ fill 7 1 nothing ∥ fill 1 1 (just navy)
                       ∥ fill 1 1 (just skyblue) ∥ fill 1 1 (just cyan) ∥ fill 1 1 (just skyblue)
                       ∥ fill 1 1 (just navy)
    ─ fill 8 1 nothing ∥ fill 1 1 (just navy) ∥ fill 1 1 (just skyblue) ∥ fill 2 1 (just navy)
    ─ fill 9 1 nothing ∥ fill 1 1 (just navy) ∥ fill 2 1 (just myFavouriteColour)
    ─ fill 9 2 nothing ∥ fill 2 2 (just myFavouriteColour) ∥ fill 1 2 nothing


-- Here is another example. It wraps nicely!
testTile : Tile 22 22 Pixel
testTile = quadrants base+ where

  empty : ∀ {m} → Tile m 1 Pixel
  empty .runTile k l = pastelGreen

  base : Tile 10 10 Pixel
  base .runTile k l = case k ≟ l of λ where
    (yes k≡l) → black
    (no ¬k≡l) → pastelGreen

  base+ : Tile 11 11 Pixel
  base+ = setPixel 0 10 purple
        $ setPixel 1 9 parma
        $ setPixel 2 9 purple
        $ setPixel 1 8 purple
        $ transpose empty ∥ setPixel 9 0 black base ─ empty

-- And here is a more basic base tile for wrapping.
baseTile : Tile 10 1 Pixel
baseTile = leftmost ∥ hMirror leftmost where

  leftmost : Tile 5 1 Pixel
  leftmost = (Tile 1 1 Pixel ∋ mkTile (λ _ _ → white)) ∥ mkTile (λ _ _ → black)

------------------------------------------------------------------------
-- Main function
------------------------------------------------------------------------

90degreeRotation : Tile w h A → Tile h w A
90degreeRotation {h = h} (mkTile runTile₁) = mkTile (λ x x₁ → runTile₁ x₁ (complement {h} x ))

-- could have used 90 degree rotation two times, but function would be 2 times slower
180degreeRotation : Tile w h A → Tile w h A
180degreeRotation {w = w} {h = h} (mkTile runTile₁) = mkTile (λ x x₁ →  runTile₁ (complement {w} x) (complement {h} x₁ ))

-- could have used 90 and 180 degree rotation but function would be 2 times slower
270degreeRotation : Tile w h A → Tile h w A
270degreeRotation {w = w} (mkTile runTile₁) = mkTile (λ x x₁ → runTile₁ (complement {w} x₁) x)

invertWord8 : Word8 → Word8
invertWord8 w = fromℕ (255 ∸ toℕ w) (ℕ.s≤s (ℕₚ.m∸n≤m 255 (toℕ w)))

-- to make it consistent with all the other picture manipulation functions, function performs inversion on a tile, not an image
colorInversion : Tile w h Pixel → Tile w h Pixel
runTile (colorInversion (mkTile runTile₁)) x x₁ with runTile₁ x x₁
runTile (colorInversion (mkTile runTile₁)) x x₁ | mkPixel red green blue = mkPixel (invertWord8 red) (invertWord8 green) (invertWord8 blue)

-- test = {! (toImage (colorInversion (fromImage blueSquare)))!} turns full blue square into yellow square as expected
-- test = {! toImage (colorInversion (fromImage redSquare))!}  turns full red into turquoise as expected



main : Main
main = run do
     --savePngImage "test.png"
     --  $ Image 1500 500 ∋_
     --  $ wrapTile
     --  $ scale 4
     --  $ flower
     putStrLn "Enter a file name to save an image to"
     input <- getLine
     savePngImage (input ++ ".png") $ (myImage)


-- Feel free to play around with the main function. You probably want
-- to at least save your image as a PNG as well!

------------------------------------------------------------------------
-- Extend the project (15 MARKS) --------- 90,180,270 degree rotation, CLI for selecting file to save, color inversion
------------------------------------------------------------------------

-- Again the final marks will be awarded for interesting extensions to
-- the above program. You might want to include a simple command line
-- interface for selecting which file to save to. Here are some other
-- ideas for what you could do:
-- * Rather than just writing images, you could dig into the JuicyPixels API [1]
--   and also support reading images
-- * Write a combinator for nesting an image into itself
-- * Implements image effects such as blur, staggered columns/rows, fade, ...
--
-- Marks will be awarded based on how interesting the program is, how
-- elegant and readable the code is, and for making good use of the
-- type system.
--
-- [1] https://hackage.haskell.org/package/JuicyPixels
