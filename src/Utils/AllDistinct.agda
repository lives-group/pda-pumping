module Utils.AllDistinct where

open import Data.List using (List; []; _∷_; _++_; map; concatMap; length)
open import Data.List.Membership.Propositional using (_∈_; _∉_; find)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-concatMap⁻)
import Data.List.Relation.Unary.Any as Any
open Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; suc; _≤_; z≤n; s≤s)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)

-- AllDistinct xs: no element appears more than once

data AllDistinct {A : Set} : List A → Set where
  [] : AllDistinct []
  _∷_ : {x : A} {xs : List A} → x ∉ xs → AllDistinct xs → AllDistinct (x ∷ xs)

-- Projections

head∉ : {A : Set} {x : A} {xs : List A} → AllDistinct (x ∷ xs) → x ∉ xs
head∉ (h ∷ _) = h

tail-dist : {A : Set} {x : A} {xs : List A} → AllDistinct (x ∷ xs) → AllDistinct xs
tail-dist (_ ∷ t) = t

allDistinct-nil : {A : Set} → AllDistinct {A} []
allDistinct-nil = []

allDistinct-singleton : {A : Set} {x : A} → AllDistinct (x ∷ [])
allDistinct-singleton = (λ ()) ∷ []

-- Closure lemmas

allDistinct-map : {A B : Set} {f : A → B}
                → (∀ {x y} → f x ≡ f y → x ≡ y)
                → {xs : List A} → AllDistinct xs → AllDistinct (map f xs)
allDistinct-map _ [] = []
allDistinct-map {f = f} inj {xs = x ∷ xs} (x∉xs ∷ dist) =
  go ∷ allDistinct-map inj dist
  where
    go : f x ∉ map f xs
    go fx∈ with ∈-map⁻ f fx∈
    ... | z , z∈xs , fz≡fx with inj fz≡fx
    ... | refl = x∉xs z∈xs

allDistinct-++ : {A : Set} {xs ys : List A}
               → AllDistinct xs → AllDistinct ys
               → (∀ {x} → x ∈ xs → x ∉ ys)
               → AllDistinct (xs ++ ys)
allDistinct-++ {xs = []} [] distYs _ = distYs
allDistinct-++ {xs = z ∷ zs} {ys = ys} (z∉zs ∷ distZs) distYs disj =
  go ∷ allDistinct-++ distZs distYs (λ m → disj (there m))
  where
    go : z ∉ zs ++ ys
    go mem with ∈-++⁻ zs mem
    ... | inj₁ m = z∉zs m
    ... | inj₂ m = disj (here refl) m

allDistinct-concatMap : {A B : Set} {f : A → List B}
  → (intra : ∀ a → AllDistinct (f a))
  → (inter : ∀ {a₁ a₂} → a₁ ≢ a₂ → ∀ {b} → b ∈ f a₁ → b ∉ f a₂)
  → {xs : List A} → AllDistinct xs
  → AllDistinct (concatMap f xs)
allDistinct-concatMap _ _ [] = []
allDistinct-concatMap {f = f} intra inter {xs = a ∷ as} (a∉as ∷ distAs) =
  allDistinct-++ (intra a) (allDistinct-concatMap intra inter distAs) go
  where
    go : ∀ {b} → b ∈ f a → b ∉ concatMap f as
    go {b} b∈fa b∈concat with find (∈-concatMap⁻ f b∈concat)
    ... | a' , a'∈as , b∈fa' = inter a≢a' b∈fa b∈fa'
      where
        a≢a' : a ≢ a'
        a≢a' refl = a∉as a'∈as

allDistinct-prefix : {A : Set} {xs ys : List A} → AllDistinct (xs ++ ys) → AllDistinct xs
allDistinct-prefix {xs = []} _ = []
allDistinct-prefix {xs = x ∷ xs} dist =
  (λ x∈xs → head∉ dist (∈-++⁺ˡ x∈xs)) ∷ allDistinct-prefix (tail-dist dist)

allDistinct-fresh : {A : Set} {xs : List A} {a : A} {ys : List A}
                  → AllDistinct (xs ++ a ∷ ys) → a ∉ xs
allDistinct-fresh {xs = []} _ ()
allDistinct-fresh {xs = x ∷ xs} dist (here a≡x) =
  head∉ dist (subst (λ z → x ∈ xs ++ z ∷ _) (sym a≡x) (∈-++⁺ʳ xs (here refl)))
allDistinct-fresh {xs = x ∷ xs} dist (there a∈xs) =
  allDistinct-fresh (tail-dist dist) a∈xs

-- remove1, membership, and length bound

remove1 : {A : Set} → (∀ (x y : A) → Dec (x ≡ y)) → A → List A → List A
remove1 _ _ [] = []
remove1 dV x (y ∷ ys) with dV x y
... | yes _ = ys
... | no _ = y ∷ remove1 dV x ys

∈-remove1 : {A : Set} (dV : ∀ (x y : A) → Dec (x ≡ y))
          → ∀ {x y : A} {xs : List A}
          → y ∈ xs → y ≢ x → y ∈ remove1 dV x xs
∈-remove1 dV {x} {xs = z ∷ _} (here refl) y≢x with dV x z
... | yes refl = ⊥-elim (y≢x refl)
... | no _ = here refl
∈-remove1 dV {x} {xs = z ∷ _} (there m) y≢x with dV x z
... | yes _ = m
... | no _ = there (∈-remove1 dV m y≢x)

remove1-⊆ : {A : Set} (dV : ∀ (x y : A) → Dec (x ≡ y))
           → ∀ {x y : A} {xs : List A}
           → y ∈ remove1 dV x xs → y ∈ xs
remove1-⊆ dV {x} {xs = z ∷ zs} m with dV x z
... | yes _ = there m
... | no _ with m
... | here refl = here refl
... | there m' = there (remove1-⊆ dV m')

remove1-length : {A : Set} (dV : ∀ (x y : A) → Dec (x ≡ y))
               → ∀ {x : A} {xs : List A}
               → x ∈ xs → suc (length (remove1 dV x xs)) ≡ length xs
remove1-length dV {x} {xs = z ∷ _} (here refl) with dV x z
... | yes _ = refl
... | no x≢z = ⊥-elim (x≢z refl)
remove1-length dV {x} {xs = z ∷ _} (there m) with dV x z
... | yes _ = refl
... | no _ = cong suc (remove1-length dV m)

allDistinct-remove1 : {A : Set} (dV : ∀ (x y : A) → Dec (x ≡ y))
                    → ∀ {x : A} {xs : List A}
                    → AllDistinct xs → AllDistinct (remove1 dV x xs)
allDistinct-remove1 _ {xs = []} [] = []
allDistinct-remove1 dV {x} {xs = y ∷ ys} (y∉ys ∷ d) with dV x y
... | yes _ = d
... | no _ = (λ m → y∉ys (remove1-⊆ dV m)) ∷ allDistinct-remove1 dV d

allDistinct-len-bound : {A : Set} (dV : ∀ (x y : A) → Dec (x ≡ y))
                      → ∀ {xs allV : List A}
                      → AllDistinct xs
                      → (∀ y → y ∈ xs → y ∈ allV)
                      → length xs ≤ length allV
allDistinct-len-bound _ {[]} [] _ = z≤n
allDistinct-len-bound dV {x ∷ xs} (x∉xs ∷ d) sub =
  let x∈allV = sub x (here refl)
      sub' = λ y y∈xs →
                  ∈-remove1 dV (sub y (there y∈xs))
                    (λ y≡x → x∉xs (subst (_∈ xs) y≡x y∈xs))
      ih = allDistinct-len-bound dV d sub'
  in subst (suc (length xs) ≤_) (remove1-length dV x∈allV) (s≤s ih)
