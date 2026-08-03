module Utils.Nat where

open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- iterate f n times

iterN : ∀ {A : Set} → ℕ → (A → A) → A → A
iterN zero _ x = x
iterN (suc n) f x = iterN n f (f x)

iterN-comm : ∀ {A : Set} (f : A → A) k x → iterN k f (f x) ≡ f (iterN k f x)
iterN-comm f zero x = refl
iterN-comm f (suc k) x = iterN-comm f k (f x)

∸-suc-lemma : ∀ m n → m < n → n ∸ m ≡ suc (n ∸ suc m)
∸-suc-lemma _ zero ()
∸-suc-lemma zero (suc n) _ = refl
∸-suc-lemma (suc m) (suc n) (s≤s lt) = ∸-suc-lemma m n lt
