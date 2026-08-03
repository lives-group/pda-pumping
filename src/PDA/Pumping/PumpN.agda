-- Well-founded core of the recursion securing |vy|≥1 (Part 2).
--
-- `pump-go` is the generic engine: given a `step` function that, for any
-- accepting run of w, returns EITHER the pumping statement P OR a
-- STRICTLY shorter accepting run of the same w, it iterates on `compLen`
-- until P is obtained.  (The caseLow-N/caseHigh-N dichotomy supplies `step`;
-- transporting the pumped word is left to pda-pumping-N.)
module PDA.Pumping.PumpN where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; ∃-syntax; Σ; _,_)

open import PDA.Base using (PDA; _⊢ₚ_⟹*_; compLen)

-- Outcome of one round of the dichotomy on the run d':
--   inj₁ P            : pumping already holds (the loop reads ≥1)
--   inj₂ (run d'' of w with compLen d'' < compLen d')  : the loop reads 0
StepOut : {Q T Γ : Set} (M : PDA Q T Γ) (q₀ : Q) (w : List T) (z : Γ)
          (P : Set) {q' : Q}
        → M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q' , [] , []) → Set
StepOut M q₀ w z P {q'} d' =
  P ⊎ (∃ λ q'' → Σ (M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q'' , [] , []))
                    λ d'' → compLen d'' < compLen d')

-- WF engine: iterate step, decreasing compLen, until it yields P.
pump-go : {Q T Γ : Set} {M : PDA Q T Γ} {q₀ : Q} {w : List T} {z : Γ} {P : Set}
        → (step : ∀ {q' : _} (d' : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q' , [] , []))
                  → StepOut M q₀ w z P d')
        → ∀ {q' : _} (d' : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q' , [] , []))
        → Acc _<_ (compLen d') → P
pump-go step d' (acc rec) with step d'
... | inj₁ p = p
... | inj₂ (q'' , d'' , lt) = pump-go step d'' (rec lt)

-- Entry point: starts the recursion from well-foundedness of <.
pump-run : {Q T Γ : Set} {M : PDA Q T Γ} {q₀ : Q} {w : List T} {z : Γ} {P : Set}
         → (step : ∀ {q' : _} (d' : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q' , [] , []))
                   → StepOut M q₀ w z P d')
         → ∀ {q_f : _} (d : M ⊢ₚ (q₀ , w , z ∷ []) ⟹* (q_f , [] , [])) → P
pump-run step d = pump-go step d (<-wellFounded (compLen d))
