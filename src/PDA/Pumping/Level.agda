module PDA.Pumping.Level where

open import Data.List using (List; []; _∷_; _++_; map; concatMap; length; lookup)
open import Data.List.Properties using (length-map; length-++)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (pigeonhole; toℕ<n)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-pred)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there; index)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

open import CFG.Base using (Finite; mkFinite; elems; complete; distinct)
open import Utils.Finite using (finite-×; finite-Maybe)
open import Utils.AllDistinct using (AllDistinct; []; _∷_; allDistinct-map)

open import PDA.Base using (PDA; Config; _⊢ₚ_⟹*_; compLen)
open import PDA.Trace using (sₕ; stateAt; stackAt)

-- ────────────────────────────────────────────────────────────────
-- Finiteness transported along a bijection
-- ────────────────────────────────────────────────────────────────

finite-iso : {A B : Set} (f : A → B) (g : B → A)
           → (∀ b → f (g b) ≡ b)
           → (∀ {x y} → f x ≡ f y → x ≡ y)
           → Finite A → Finite B
finite-iso f g fg finj finA = mkFinite (map f (elems finA)) comp dist
  where
    comp : ∀ b → b ∈ map f (elems finA)
    comp b rewrite sym (fg b) = ∈-map⁺ f (complete finA (g b))
    dist : AllDistinct (map f (elems finA))
    dist = allDistinct-map finj (distinct finA)

-- ────────────────────────────────────────────────────────────────
-- Fixed-length vectors over a finite type
-- ────────────────────────────────────────────────────────────────

finite-Vec : {A : Set} → Finite A → (n : ℕ) → Finite (Vec A n)
finite-Vec fin zero = mkFinite ([] ∷ []) (λ { [] → here refl }) ((λ ()) ∷ [])
finite-Vec fin (suc n) =
  finite-iso into outof iso-id into-inj (finite-× fin (finite-Vec fin n))
  where
    into : _ → Vec _ (suc n)
    into (a , v) = a ∷ v
    outof : Vec _ (suc n) → _
    outof (a ∷ v) = a , v
    iso-id : ∀ v → into (outof v) ≡ v
    iso-id (a ∷ v) = refl
    into-inj : ∀ {x y} → into x ≡ into y → x ≡ y
    into-inj {a , v} {a' , v'} refl = refl

-- ────────────────────────────────────────────────────────────────
-- Cardinalities
-- ────────────────────────────────────────────────────────────────

card-Maybe : {A : Set} (fin : Finite A)
           → length (elems (finite-Maybe fin)) ≡ suc (length (elems fin))
card-Maybe fin = cong suc (length-map just (elems fin))

private
  len-cm : {A B : Set} (as : List A) (bs : List B)
         → length (concatMap (λ a → map (a ,_) bs) as) ≡ length as * length bs
  len-cm [] bs = refl
  len-cm (a ∷ as) bs =
    trans (length-++ (map (a ,_) bs))
          (cong₂ _+_ (length-map (a ,_) bs) (len-cm as bs))

card-× : {A B : Set} (fA : Finite A) (fB : Finite B)
       → length (elems (finite-× fA fB)) ≡ length (elems fA) * length (elems fB)
card-× fA fB = len-cm (elems fA) (elems fB)

card-Vec : {A : Set} (fin : Finite A) (n : ℕ)
         → length (elems (finite-Vec fin n)) ≡ length (elems fin) ^ n
card-Vec fin zero = refl
card-Vec fin (suc n) = begin
  length (elems (finite-Vec fin (suc n)))
    ≡⟨ length-map _ (elems (finite-× fin (finite-Vec fin n))) ⟩
  length (elems (finite-× fin (finite-Vec fin n)))
    ≡⟨ card-× fin (finite-Vec fin n) ⟩
  length (elems fin) * length (elems (finite-Vec fin n))
    ≡⟨ cong (length (elems fin) *_) (card-Vec fin n) ⟩
  length (elems fin) ^ suc n ∎

-- ────────────────────────────────────────────────────────────────
-- The top-l view of a stack (with padding) and the configuration type
--
-- topl l s : the l topmost symbols of s, padded with nothing
-- when the stack holds fewer than l symbols.
-- ────────────────────────────────────────────────────────────────

topl : {Γ : Set} (l : ℕ) → List Γ → Vec (Maybe Γ) l
topl zero _ = []
topl (suc l) [] = nothing ∷ topl l []
topl (suc l) (x ∷ xs) = just x ∷ topl l xs

-- The top-L view is faithful (injective) on stacks of height ≤ L.
topl-inj : {Γ : Set} (L : ℕ) {s s' : List Γ}
         → length s ≤ L → length s' ≤ L → topl L s ≡ topl L s' → s ≡ s'
topl-inj zero {[]} {[]} _ _ _ = refl
topl-inj zero {_ ∷ _} {_} () _ _
topl-inj zero {[]} {_ ∷ _} _ () _
topl-inj (suc L) {[]} {[]} _ _ _ = refl
topl-inj (suc L) {[]} {_ ∷ _} _ _ eq with ∷-injectiveˡ eq
... | ()
topl-inj (suc L) {_ ∷ _} {[]} _ _ eq with ∷-injectiveˡ eq
... | ()
topl-inj (suc L) {x ∷ xs} {y ∷ ys} le le' eq =
  cong₂ _∷_ (just-injective (∷-injectiveˡ eq))
            (topl-inj L (≤-pred le) (≤-pred le') (∷-injectiveʳ eq))

-- Configuration in the sense of the paper: state + the l topmost symbols.
Cfg : (Q Γ : Set) → ℕ → Set
Cfg Q Γ l = Q × Vec (Maybe Γ) l

finite-Cfg : {Q Γ : Set} → Finite Q → Finite Γ → (l : ℕ) → Finite (Cfg Q Γ l)
finite-Cfg finQ finΓ l = finite-× finQ (finite-Vec (finite-Maybe finΓ) l)

-- |Cfg| = |Q| · (|Γ|+1)^l
card-Cfg : {Q Γ : Set} (finQ : Finite Q) (finΓ : Finite Γ) (l : ℕ)
         → length (elems (finite-Cfg finQ finΓ l))
           ≡ length (elems finQ) * (suc (length (elems finΓ)) ^ l)
card-Cfg finQ finΓ l = begin
  length (elems (finite-Cfg finQ finΓ l))
    ≡⟨ card-× finQ (finite-Vec (finite-Maybe finΓ) l) ⟩
  length (elems finQ) * length (elems (finite-Vec (finite-Maybe finΓ) l))
    ≡⟨ cong (length (elems finQ) *_) vecCard ⟩
  length (elems finQ) * (suc (length (elems finΓ)) ^ l) ∎
  where
    vecCard : length (elems (finite-Vec (finite-Maybe finΓ) l))
              ≡ suc (length (elems finΓ)) ^ l
    vecCard = begin
      length (elems (finite-Vec (finite-Maybe finΓ) l))
        ≡⟨ card-Vec (finite-Maybe finΓ) l ⟩
      length (elems (finite-Maybe finΓ)) ^ l
        ≡⟨ cong (_^ l) (card-Maybe finΓ) ⟩
      suc (length (elems finΓ)) ^ l ∎

-- ────────────────────────────────────────────────────────────────
-- N-levels and configuration-at-a-position (the paper's definitions)
--
-- IsNLevel d N i j k : the stack grows by N from i to j and shrinks by N
-- from j to k, returning to the initial height (sᵢ = s_k), staying in range.
-- ────────────────────────────────────────────────────────────────

IsNLevel : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
         → (d : M ⊢ₚ c₁ ⟹* c₂) (N i j k : ℕ) → Set
IsNLevel d N i j k =
    i < j × j < k × k ≤ compLen d
  × sₕ i d ≡ sₕ k d
  × sₕ j d ≡ sₕ i d + N
  × (∀ n → i ≤ n → n ≤ j → (sₕ i d ≤ sₕ n d) × (sₕ n d ≤ sₕ j d))
  × (∀ n → j ≤ n → n ≤ k → (sₕ k d ≤ sₕ n d) × (sₕ n d ≤ sₕ j d))

-- Configuration in the sense of the paper: state + the top-l view of the stack.
cfgAt : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
      → (l k : ℕ) → M ⊢ₚ c₁ ⟹* c₂ → Cfg Q Γ l
cfgAt l k d = stateAt k d , topl l (stackAt k d)

-- ────────────────────────────────────────────────────────────────
-- Pigeonhole principle over positions (the engine of both cases)
--
-- A function from positions 0..n-1 into a finite type C with fewer than n
-- elements must collide: ∃ i<j<n with f i ≡ f j.  (via Data.Fin pigeonhole)
-- ────────────────────────────────────────────────────────────────

private
  idx : {C : Set} (finC : Finite C) → C → Fin (length (elems finC))
  idx finC c = index (complete finC c)

  idx-inj : {C : Set} (finC : Finite C) {c c' : C}
          → idx finC c ≡ idx finC c' → c ≡ c'
  idx-inj finC {c} {c'} eq = begin
    c                                  ≡⟨ lookup-index (complete finC c) ⟩
    lookup (elems finC) (idx finC c)   ≡⟨ cong (lookup (elems finC)) eq ⟩
    lookup (elems finC) (idx finC c')  ≡⟨ sym (lookup-index (complete finC c')) ⟩
    c'                                 ∎

config-collision : {C : Set} (finC : Finite C)
                 → (f : ℕ → C) (n : ℕ)
                 → length (elems finC) < n
                 → ∃ λ i → ∃ λ j → i < j × j < n × f i ≡ f j
config-collision finC f n m<n
  with pigeonhole m<n (λ i → idx finC (f (toℕ i)))
... | i , j , i<j , eq = toℕ i , toℕ j , i<j , toℕ<n j , idx-inj finC eq

-- Version with domain Fin (suc m): useful when there are exactly suc m items
-- (the p′+1 heights) and the finite type has ≤ m elements.
config-collision-Fin : {C : Set} (finC : Finite C) (m : ℕ) (f : Fin (suc m) → C)
                     → length (elems finC) ≤ m
                     → ∃ λ i → ∃ λ j → toℕ i < toℕ j × f i ≡ f j
config-collision-Fin finC m f card≤m
  with pigeonhole (s≤s card≤m) (λ i → idx finC (f i))
... | i , j , i<j , eq = i , j , i<j , idx-inj finC eq
