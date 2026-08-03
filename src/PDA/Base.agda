module PDA.Base where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)

-- ────────────────────────────────────────────────────────────────
-- Nondeterministic pushdown automaton (PDA)
--
-- Q : type of states
-- T : type of terminals (the input alphabet)
-- Γ : type of stack symbols
--
-- δ(q, a, A) returns a list of pairs (new state, new stack):
-- in state q, reading the symbol a (or nothing = ε-transition), with
-- A on top of the stack, replace A by the string β and move to r.
-- ────────────────────────────────────────────────────────────────

record PDA (Q T Γ : Set) : Set where
  field
    δ : Q → Maybe T → Γ → List (Q × List Γ)
    q₀ : Q -- initial state
    z₀ : Γ -- initial stack symbol
    isFinal : Q → Bool -- predicate for final states

open PDA public

-- Instantaneous configuration: (state, remaining input, stack)
Config : Set → Set → Set → Set
Config Q T Γ = Q × List T × List Γ

-- ────────────────────────────────────────────────────────────────
-- One-step computation relation
--
-- M ⊢ₚ c₁ ⟹ c₂ : configuration c₂ is obtained from c₁ by one step
-- of the PDA M, popping the top symbol A and pushing β.
-- ────────────────────────────────────────────────────────────────

data _⊢ₚ_⟹_ {Q T Γ : Set} (M : PDA Q T Γ)
    : Config Q T Γ → Config Q T Γ → Set where

  read : {q r : Q} {a : T} {w : List T} {A : Γ} {β γ : List Γ}
       → (r , β) ∈ M .δ q (just a) A
       → M ⊢ₚ (q , a ∷ w , A ∷ γ) ⟹ (r , w , β ++ γ)

  eps : {q r : Q} {w : List T} {A : Γ} {β γ : List Γ}
       → (r , β) ∈ M .δ q nothing A
       → M ⊢ₚ (q , w , A ∷ γ) ⟹ (r , w , β ++ γ)

-- ────────────────────────────────────────────────────────────────
-- Reflexive-transitive closure of the step relation
-- ────────────────────────────────────────────────────────────────

data _⊢ₚ_⟹*_ {Q T Γ : Set} (M : PDA Q T Γ)
    : Config Q T Γ → Config Q T Γ → Set where

  ε : {c : Config Q T Γ} → M ⊢ₚ c ⟹* c

  _◅_ : {c₁ c₂ c₃ : Config Q T Γ}
      → M ⊢ₚ c₁ ⟹ c₂
      → M ⊢ₚ c₂ ⟹* c₃
      → M ⊢ₚ c₁ ⟹* c₃

infixr 5 _◅_

-- ────────────────────────────────────────────────────────────────
-- Basic lemmas
-- ────────────────────────────────────────────────────────────────

⟹*ₚ-trans : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ c₃ : Config Q T Γ}
           → M ⊢ₚ c₁ ⟹* c₂ → M ⊢ₚ c₂ ⟹* c₃ → M ⊢ₚ c₁ ⟹* c₃
⟹*ₚ-trans ε d₂ = d₂
⟹*ₚ-trans (s ◅ d₁) d₂ = s ◅ ⟹*ₚ-trans d₁ d₂

⟹ₚ→⟹*ₚ : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
         → M ⊢ₚ c₁ ⟹ c₂ → M ⊢ₚ c₁ ⟹* c₂
⟹ₚ→⟹*ₚ s = s ◅ ε

-- Measure of a computation: its number of steps
compLen : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
        → M ⊢ₚ c₁ ⟹* c₂ → ℕ
compLen ε = zero
compLen (_ ◅ d) = suc (compLen d)
