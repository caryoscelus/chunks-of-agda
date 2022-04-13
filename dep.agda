{-# OPTIONS --without-K --safe #-}

{-

dependent types make a lot of things possible, including
type-safe arbitrary argument count functions. however, if
what's we're interested in is computation and making sure
that the computation is correct, we don't need to preserve
dependent types in compiled code: we only need to make sure
the runtime code is correct during compile-time. often
this is done via "erasure", that is, ignoring irrelevant
bits of computation. but it is unclear how one is to erase
arbitrary argument function. what if we can find
non-dependent calculation that provably does the same job?
this file is just a start in that direction, exploring how
 such a transformation can be done manually, in order to
then find automated solution

-}

module dep where

open import Data.Nat
import Data.List as L
open import Data.List using (List)
import Data.Vec as V
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality
open import Function.Core

Fn : ℕ → Set
Fn zero = ℕ
Fn (suc n) = ℕ → Fn n

app-n : ∀ {n} → Vec ℕ n → Fn n → ℕ
app-n V.[] x = x
app-n (x V.∷ xs) f = app-n xs (f x)

_<+>_ : ∀ {n} → Fn n → Fn n → Fn n
_<+>_ {zero} x y = x + y
_<+>_ {suc n} f g = λ x → f x <+> g x

const-n : ∀ {n} → ℕ → Fn n
const-n {zero} x = x
const-n {suc n} x = λ _ → const-n x

add-n : ∀ n → Fn n
add-n zero = 0
add-n (suc n) = λ x → const-n x <+> add-n n

sum : List ℕ → ℕ
sum L.[] = 0
sum (x L.∷ xs) = x + sum xs

sum' : List ℕ → ℕ
sum' x = app-n (V.fromList x) (add-n (L.length x))

module _ where
  open ≡-Reasoning

  app-const-n-eq : ∀ xs {n} → app-n (V.fromList xs) (const-n n) ≡ n
  app-const-n-eq L.[] = refl
  app-const-n-eq (x L.∷ xs) = app-const-n-eq xs

  app-<+>-eq : ∀ {n} {f g : Fn n} xs →
    app-n xs (f <+> g) ≡ app-n xs f + app-n xs g
  app-<+>-eq V.[] = refl
  app-<+>-eq (x V.∷ xs) = app-<+>-eq xs

  sum-eq : ∀ x → sum' x ≡ sum x
  sum-eq L.[] = refl
  sum-eq (x L.∷ xs) = begin
    sum' (x L.∷ xs)
      ≡⟨ refl ⟩
    app-n (V.fromList (x L.∷ xs)) (add-n (L.length (x L.∷ xs)))
      ≡⟨ refl ⟩
    app-n (V.fromList xs) (const-n x <+> add-n (L.length xs))
      ≡⟨ app-<+>-eq (V.fromList xs) ⟩
    app-n (V.fromList xs) (const-n x) +
      app-n (V.fromList xs) (add-n (L.length xs))
      ≡⟨ cong (_+ _) (app-const-n-eq xs) ⟩
    x + app-n (V.fromList xs) (add-n (L.length xs))
      ≡⟨ cong (x +_) (sum-eq xs) ⟩
    x + sum xs ∎
