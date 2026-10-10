-- Pumping for a normal PDA (IsNormalPDA), stated for an arbitrary
-- computation from a one-symbol stack down to the empty stack, with BOTH
-- endpoints fixed.  This is the form used inside an excursion by the
-- bounded theorem (PDA.Pumping.Bounded): the pumped runs end in the same
-- state q_f as the original one, so they can be plugged back in context.
--
--   pda-pumping-N-at : |vy| ≥ 1 by well-founded recursion on compLen
--                      (via pump-run), no bound on |vxy|.
module PDA.Pumping.PumpNormal where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤?_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-<-trans; ≰⇒>; +-identityʳ)
open import Data.Product using (Σ; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import CFG.Base using (Finite)
open import PDA.Base using (PDA; _⊢ₚ_⟹*_; compLen)
open import PDA.Normal using (IsNormalPDA)
open import PDA.Trace using (rep; sₕ)
open import PDA.Pumping.Height using (argmax)
open import PDA.Pumping.Lemma using (fullStates; pumpLen; card-Cfg-mono; rep-[])
open import PDA.Pumping.CaseLow using (caseLow-N)
open import PDA.Pumping.CaseHigh using (caseHigh-N)
open import PDA.Pumping.PumpN using (StepOut; pump-run)

-- The pumping statement for runs from (q₀ , w , z ∷ []) to (q_f , [] , []),
-- kept at top level so that a `with` abstraction inside a `where` does not
-- generalize metavariables over the whole outer telescope, which blows up
-- type-checking memory.
PumpAt : {Q T Γ : Set} (M : PDA Q T Γ) (q₀ : Q) (z : Γ) (q_f : Q) (w : List T) → Set
PumpAt M q₀ z q_f w = ∃ λ u → ∃ λ v → ∃ λ x → ∃ λ y → ∃ λ z'
            → w ≡ u ++ v ++ x ++ y ++ z'
            × 0 < length v + length y
            × (∀ k → M ⊢ₚ (q₀ , u ++ rep k v ++ x ++ rep k y ++ z' , z ∷ []) ⟹* (q_f , [] , []))

-- Input rewriting in the low case (y = z = []): eliminates rep k [] ++ [].
inputeqLow : {T : Set} (u v x : List T) (k : ℕ)
           → u ++ rep k v ++ x ++ rep k [] ++ [] ≡ u ++ rep k v ++ x
inputeqLow u v x k = cong (λ t → u ++ rep k v ++ t)
                       (trans (cong (λ r → x ++ r ++ []) (rep-[] k)) (++-identityʳ x))

-- One round of the dichotomy (top level): argmax + caseLow-N/caseHigh-N.
-- CRITICAL: the ⊎ of caseLow-N/caseHigh-N are consumed by `[_,_]′`
-- (function application), NOT by `with`: a `with` on a large sum-typed
-- scrutinee, in a context with ~13 free variables, generalizes every
-- implicit-argument goal over the telescope and makes type-checking
-- run out of memory.
pumpStep : {Q T Γ : Set} {M : PDA Q T Γ}
         → IsNormalPDA M → (finQ : Finite Q) (finΓ : Finite Γ)
         → {q₀ q_f : Q} {z : Γ} {w : List T} → pumpLen finQ finΓ < length w
         → (d' : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q_f , [] , []))
         → StepOut M q₀ w z (PumpAt M q₀ z q_f w) d'
pumpStep {M = M} norm finQ finΓ {q₀} {q_f} {z} {w} plen<w d' with argmax d' (compLen d')
... | jmax , jmax≤cl , isMax with sₕ jmax d' ≤? suc (fullStates finQ finΓ)
... | yes B≤P+1 =
        [ (λ { (u , v , x , weq , 0<v , run) →
                inj₁ (u , v , x , [] , []
                     , trans weq (cong (λ t → u ++ v ++ t) (sym (++-identityʳ x)))
                     , subst (0 <_) (sym (+-identityʳ (length v))) 0<v
                     , λ k → subst (λ inp → M ⊢ₚ (q₀ , inp , z ∷ []) ⟹* (q_f , [] , []))
                                   (sym (inputeqLow u v x k)) (run k)) })
        , inj₂
        ]′ (caseLow-N finQ finΓ d' (sₕ jmax d') isMax
              (≤-<-trans (card-Cfg-mono finQ finΓ B≤P+1) plen<w))
... | no B>P+1 =
        [ inj₁
        , inj₂
        ]′ (caseHigh-N norm finQ finΓ d' jmax jmax≤cl 1 (fullStates finQ finΓ)
              (s≤s z≤n) (≰⇒> B>P+1) ≤-refl)

pda-pumping-N-at : {Q T Γ : Set} {M : PDA Q T Γ}
                 → IsNormalPDA M → (finQ : Finite Q) (finΓ : Finite Γ)
                 → {q₀ q_f : Q} {z : Γ} {w : List T}
                 → M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q_f , [] , [])
                 → pumpLen finQ finΓ < length w
                 → PumpAt M q₀ z q_f w
pda-pumping-N-at norm finQ finΓ d plen<w = pump-run (pumpStep norm finQ finΓ plen<w) d
