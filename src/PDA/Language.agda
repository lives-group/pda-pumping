module PDA.Language where

open import Data.List using (List; []; _∷_)
open import Data.Product using (∃; ∃-syntax; _×_; _,_)

open import PDA.Base

-- ────────────────────────────────────────────────────────────────
-- Acceptance by empty stack, the criterion of the pumping lemma.
-- (No final states are needed: the PDA record has none.)
-- ────────────────────────────────────────────────────────────────

-- Acceptance by empty stack
-- The automaton exhausts the input and empties the stack, in any state.
AccES : {Q T Γ : Set} → PDA Q T Γ → List T → Set
AccES {Q} M w =
  ∃ λ (q : Q) → M ⊢ₚ (M .q₀ , w , M .z₀ ∷ []) ⟹* (q , [] , [])
