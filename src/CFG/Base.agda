module CFG.Base where

open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; ∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; ¬_)
open import Data.List.Membership.Propositional using (_∈_)

open import Utils.AllDistinct using (AllDistinct)

-- Grammar as a type-indexed function
--
-- V : abstract type of non-terminals
-- T : abstract type of terminals

Grammar : Set → Set → Set
Grammar V T = V → List (List (V ⊎ T))

liftSym : {V W T : Set} → (V → W) → V ⊎ T → W ⊎ T
liftSym f (inj₁ A) = inj₁ (f A)
liftSym f (inj₂ a) = inj₂ a

liftRHS : {V W T : Set} → (V → W) → List (V ⊎ T) → List (W ⊎ T)
liftRHS f = map (liftSym f)

liftAlts : {V W T : Set} → (V → W) → List (List (V ⊎ T)) → List (List (W ⊎ T))
liftAlts f = map (liftRHS f)

-- Extending a grammar by a single fresh non-terminal

extend₁ : {V T : Set}
        → Grammar V T -- the original grammar
        → List (List (Maybe V ⊎ T)) -- productions of the fresh non-terminal
        → Grammar (Maybe V) T
extend₁ G _ (just A) = liftAlts just (G A)
extend₁ _ prods nothing = prods

-- Extending a grammar by a block of fresh non-terminals

private
  reassocSym : {V W T : Set} → W ⊎ (V ⊎ T) → (W ⊎ V) ⊎ T
  reassocSym (inj₁ w) = inj₁ (inj₁ w)
  reassocSym (inj₂ (inj₁ A)) = inj₁ (inj₂ A)
  reassocSym (inj₂ (inj₂ a)) = inj₂ a

extendBlock : {V W T : Set}
            → (W → List (List (W ⊎ (V ⊎ T))))
            → Grammar V T
            → Grammar (W ⊎ V) T
extendBlock newRules _ (inj₁ w) = map (map reassocSym) (newRules w)
extendBlock _ G (inj₂ A) = liftAlts inj₂ (G A)

-- Evidence of finiteness and decidable equality

record Finite (A : Set) : Set where
  constructor mkFinite
  field
    elems : List A
    complete : ∀ (x : A) → x ∈ elems
    distinct : AllDistinct elems

open Finite public

DecEq : Set → Set
DecEq A = ∀ (x y : A) → Dec (x ≡ y)

-- Structural properties of grammars

NoEpsilon : {V T : Set} → Grammar V T → Set
NoEpsilon G = ∀ A → ¬ ([] ∈ G A)
