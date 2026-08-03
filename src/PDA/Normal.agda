module PDA.Normal where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PDA.Base

-- ────────────────────────────────────────────────────────────────
-- The normal form of the paper (condition *)
--
-- Every transition pops the top symbol A and then:
--   · pushes nothing        (β ≡ [])         → the stack shrinks by 1
--   · restores A, pushes X  (β ≡ X ∷ A ∷ []) → the stack grows by 1
--
-- In particular every step changes the stack height by exactly ±1,
-- and a push never disturbs what lies below the top (it restores A).
-- ────────────────────────────────────────────────────────────────

IsNormalPDA : {Q T Γ : Set} → PDA Q T Γ → Set
IsNormalPDA {Q} {T} {Γ} M =
  ∀ (q : Q) (mt : Maybe T) (A : Γ) {r : Q} {β : List Γ}
  → (r , β) ∈ M .δ q mt A
  → β ≡ [] ⊎ ∃ λ X → β ≡ X ∷ A ∷ []

-- ────────────────────────────────────────────────────────────────
-- Strengthened normal form: every READ is a pop (β ≡ []) and every
-- ε-transition is a push (β ≡ X ∷ A ∷ []).  The PDA built by the
-- construction (PDA.NormalForm) satisfies it.  It implies IsNormalPDA.
--
-- Consequence: in a loop whose endpoints have equal stack height,
-- #reads = #pushes, so a non-empty loop consumes ≥ 1 symbol
-- ────────────────────────────────────────────────────────────────

record IsNormalPDA⁺ {Q T Γ : Set} (M : PDA Q T Γ) : Set where
  field
    read-pops : ∀ (q : Q) (a : T) (A : Γ) {r : Q} {β : List Γ}
              → (r , β) ∈ M .δ q (just a) A → β ≡ []
    eps-pushes : ∀ (q : Q) (A : Γ) {r : Q} {β : List Γ}
              → (r , β) ∈ M .δ q nothing A → ∃ λ X → β ≡ X ∷ A ∷ []

open IsNormalPDA⁺ public

normal⁺⇒normal : {Q T Γ : Set} {M : PDA Q T Γ} → IsNormalPDA⁺ M → IsNormalPDA M
normal⁺⇒normal n⁺ q (just a) A mem = inj₁ (read-pops n⁺ q a A mem)
normal⁺⇒normal n⁺ q nothing A mem = inj₂ (eps-pushes n⁺ q A mem)

-- ────────────────────────────────────────────────────────────────
-- Effect of a step on the stack (abstracting away state and input)
--
-- pop  : removes the top, preserving the tail.
-- push : adds X on top, keeping the previous stack as the tail.
-- ────────────────────────────────────────────────────────────────

data StackStep {Γ : Set} : List Γ → List Γ → Set where
  pop : ∀ {A γ} → StackStep (A ∷ γ) γ
  push : ∀ {X A γ} → StackStep (A ∷ γ) (X ∷ A ∷ γ)

stkOf : {Q T Γ : Set} → Config Q T Γ → List Γ
stkOf (_ , _ , s) = s

-- Every step of a normal PDA is a pop or a push on the stack.
normal-step : {Q T Γ : Set} {M : PDA Q T Γ} → IsNormalPDA M
            → ∀ {c₁ c₂ : Config Q T Γ} → M ⊢ₚ c₁ ⟹ c₂
            → StackStep (stkOf c₁) (stkOf c₂)
normal-step norm (read {q} {a = a} {A = A} mem) with norm q (just a) A mem
... | inj₁ refl = pop
... | inj₂ (_ , refl) = push
normal-step norm (eps {q} {A = A} mem) with norm q nothing A mem
... | inj₁ refl = pop
... | inj₂ (_ , refl) = push

-- Every step changes the stack height by exactly ±1.
stackStep-±1 : {Γ : Set} {s s' : List Γ}
             → StackStep s s'
             → (length s ≡ suc (length s')) ⊎ (length s' ≡ suc (length s))
stackStep-±1 pop = inj₁ refl
stackStep-±1 push = inj₂ refl

-- A pop exposes exactly the tail of the previous stack.
stackStep-pop : {Γ : Set} {s s' : List Γ}
              → StackStep s s' → length s' ≡ suc (length s) ⊎ (∃ λ A → s ≡ A ∷ s')
stackStep-pop pop = inj₂ (_ , refl)
stackStep-pop push = inj₁ refl

-- A push keeps the previous stack as its tail (nothing below the top changes).
stackStep-push : {Γ : Set} {s s' : List Γ}
               → StackStep s s' → (length s ≡ suc (length s')) ⊎ (∃ λ X → s' ≡ X ∷ s)
stackStep-push pop = inj₁ refl
stackStep-push push = inj₂ (_ , refl)
