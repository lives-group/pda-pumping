module PDA.Language where

open import Data.Bool using (Bool; true; false; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃; ∃-syntax; _×_; _,_)

open import PDA.Base

-- ────────────────────────────────────────────────────────────────
-- Acceptance criteria for a PDA
--
-- Three standard criteria, provably equivalent (see
-- PDA.Equivalence):
--   ES  : by empty stack
--   FS  : by final state
--   FES : by final state with empty stack
-- ────────────────────────────────────────────────────────────────

-- Acceptance by empty stack
-- The automaton exhausts the input and empties the stack, in any state.
AccES : {Q T Γ : Set} → PDA Q T Γ → List T → Set
AccES {Q} M w =
  ∃ λ (q : Q) → M ⊢ₚ (M .q₀ , w , M .z₀ ∷ []) ⟹* (q , [] , [])

-- Acceptance by final state
-- The automaton exhausts the input in a final state, with an arbitrary stack.
AccFS : {Q T Γ : Set} → PDA Q T Γ → List T → Set
AccFS {Q} {T} {Γ} M w =
  ∃ λ (q : Q) → ∃ λ (γ : List Γ)
  → M ⊢ₚ (M .q₀ , w , M .z₀ ∷ []) ⟹* (q , [] , γ)
  × M .isFinal q ≡ true
  where open import Relation.Binary.PropositionalEquality using (_≡_)

-- Acceptance by final state with empty stack
-- Combines the two criteria above.
AccFES : {Q T Γ : Set} → PDA Q T Γ → List T → Set
AccFES {Q} M w =
  ∃ λ (q : Q)
  → M ⊢ₚ (M .q₀ , w , M .z₀ ∷ []) ⟹* (q , [] , [])
  × M .isFinal q ≡ true
  where open import Relation.Binary.PropositionalEquality using (_≡_)
