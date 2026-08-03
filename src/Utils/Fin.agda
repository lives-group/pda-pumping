module Utils.Fin where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map; length; lookup; drop)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _×_; _,_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Utils.Maybe using (just-inj; map-just; map-nothing)

-- enumerate all elements of Fin n

allFins : (n : ℕ) → List (Fin n)
allFins zero = []
allFins (suc n) = fzero ∷ map fsuc (allFins n)

allFins-complete : ∀ {n} → (i : Fin n) → i ∈ allFins n
allFins-complete fzero = here refl
allFins-complete (fsuc i) = there (∈-map⁺ fsuc (allFins-complete i))

-- successor within Fin k, nothing at the last index

finSucc? : ∀ {k} → Fin k → Maybe (Fin k)
finSucc? {suc _} (fsuc j) = Data.Maybe.map fsuc (finSucc? j)
finSucc? {suc zero} fzero = nothing
finSucc? {suc (suc _)} fzero = just (fsuc fzero)

fin0? : (n : ℕ) → Maybe (Fin n)
fin0? zero = nothing
fin0? (suc _) = just fzero

finSucc?-just : ∀ {n} (j j′ : Fin n) → finSucc? j ≡ just j′ → toℕ j′ ≡ suc (toℕ j)
finSucc?-just {suc zero} fzero j′ ()
finSucc?-just {suc (suc _)} fzero j′ eq = cong toℕ (just-inj (sym eq))
finSucc?-just {suc _} (fsuc j) j′ eq with map-just (finSucc? j) j′ eq
... | j″ , ej , refl = cong suc (finSucc?-just j j″ ej)

finSucc?-last : ∀ {n} (j : Fin n) → finSucc? j ≡ nothing → suc (toℕ j) ≡ n
finSucc?-last {suc zero} fzero refl = refl
finSucc?-last {suc (suc _)} fzero ()
finSucc?-last {suc _} (fsuc j) eq = cong suc (finSucc?-last j (map-nothing (finSucc? j) eq))

finSucc?-spec : ∀ {n} (j : Fin n)
  → (finSucc? j ≡ nothing × suc (toℕ j) ≡ n)
  ⊎ (∃ λ j′ → finSucc? j ≡ just j′ × toℕ j′ ≡ suc (toℕ j))
finSucc?-spec j with finSucc? j in eq
... | nothing = inj₁ (refl , finSucc?-last j eq)
... | just j′ = inj₂ (j′ , refl , finSucc?-just j j′ eq)

drop-at-lookup : {A : Set} (xs : List A) (j : Fin (length xs))
               → drop (toℕ j) xs ≡ lookup xs j ∷ drop (suc (toℕ j)) xs
drop-at-lookup (x ∷ xs) fzero = refl
drop-at-lookup (x ∷ xs) (fsuc j) = drop-at-lookup xs j

drop-all : {A : Set} (xs : List A) → drop (length xs) xs ≡ []
drop-all [] = refl
drop-all (x ∷ xs) = drop-all xs

len0 : {A : Set} (xs : List A) → length xs ≡ 0 → xs ≡ []
len0 [] _ = refl
len0 (_ ∷ _) ()

fin0?-zero : (n : ℕ) → fin0? n ≡ nothing → n ≡ 0
fin0?-zero zero _ = refl
fin0?-zero (suc _) ()

fin0?-sucL : (n : ℕ) {j : Fin n} → fin0? n ≡ just j → ∃ λ m → n ≡ suc m
fin0?-sucL (suc m) _ = m , refl
fin0?-sucL zero ()

fin0?-fzero : (n : ℕ) {j : Fin n} → fin0? n ≡ just j → toℕ j ≡ 0
fin0?-fzero (suc _) eqF = cong toℕ (sym (just-inj eqF))
fin0?-fzero zero ()
