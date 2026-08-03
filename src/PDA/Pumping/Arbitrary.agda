-- Pumping lemma for an ARBITRARY PDA (the hypothesis is a pushdown
-- automaton; grammars are NEVER mentioned).
--
--   pda-pumping-N : generalizes pda-pumping from IsNormalPDA⁺ to IsNormalPDA
--                   (|vy|≥1 by well-founded recursion on compLen, via pump-run).
--   pumping-pda   : composes normalize (PDA→IsNormalPDA, full language)
--                   with pda-pumping-N and transports the pumped runs.
module PDA.Pumping.Arbitrary where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤?_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-<-trans; ≰⇒>; +-identityʳ)
open import Data.Maybe using (Maybe)
open import Data.Product using (Σ; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import CFG.Base using (Finite)
open import Utils.Finite using (finite-Maybe)
open import PDA.Base using (PDA; _⊢ₚ_⟹*_; compLen)
open PDA using (q₀; z₀)
open import PDA.Language using (AccES)
open import PDA.Normal using (IsNormalPDA)
open import PDA.Trace using (rep; sₕ; stackAt)
open import PDA.Pumping.Height using (argmax)
open import PDA.Pumping.Lemma using (fullStates; pumpLen; card-Cfg-mono; rep-[])
open import PDA.Pumping.CaseLow using (caseLow-N)
open import PDA.Pumping.CaseHigh using (caseHigh-N)
open import PDA.Pumping.PumpN using (StepOut; pump-run)
open import PDA.NormalizePDA using (normalize)

-- ────────────────────────────────────────────────────────────────
-- pda-pumping-N: pumping for IsNormalPDA (without ⁺).
-- ────────────────────────────────────────────────────────────────

-- The pumping statement (the P of the WF engine), kept at top level so that
-- a `with` abstraction inside a `where` does not generalize metavariables
-- over the whole outer telescope, which blows up type-checking memory.
Pump : {Q T Γ : Set} (M : PDA Q T Γ) (w : List T) → Set
Pump M w = ∃ λ u → ∃ λ v → ∃ λ x → ∃ λ y → ∃ λ z
            → w ≡ u ++ v ++ x ++ y ++ z
            × 0 < length v + length y
            × (∀ k → AccES M (u ++ rep k v ++ x ++ rep k y ++ z))

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
         → {w : List T} → pumpLen finQ finΓ < length w
         → ∀ {q' : _} (d' : M ⊢ₚ (M .q₀ , w , M .z₀ ∷ []) ⟹* (q' , [] , []))
         → StepOut M (M .q₀) w (M .z₀) (Pump M w) d'
pumpStep {M = M} norm finQ finΓ {w} plen<w {q'} d' with argmax d' (compLen d')
... | jmax , jmax≤cl , isMax with sₕ jmax d' ≤? suc (fullStates finQ finΓ)
... | yes B≤P+1 =
        [ (λ { (u , v , x , weq , 0<v , run) →
                inj₁ (u , v , x , [] , []
                     , trans weq (cong (λ t → u ++ v ++ t) (sym (++-identityʳ x)))
                     , subst (0 <_) (sym (+-identityʳ (length v))) 0<v
                     , λ k → q' , subst (λ inp → M ⊢ₚ (M .q₀ , inp , M .z₀ ∷ [])
                                                    ⟹* (q' , [] , []))
                                         (sym (inputeqLow u v x k)) (run k)) })
        , inj₂
        ]′ (caseLow-N finQ finΓ d' (sₕ jmax d') isMax
              (≤-<-trans (card-Cfg-mono finQ finΓ B≤P+1) plen<w))
... | no B>P+1 =
        [ (λ { (uw , vw , xw , yw , zw , wdecomp , vy≥1 , run) →
                inj₁ (uw , vw , xw , yw , zw , wdecomp , vy≥1 , λ k → q' , run k) })
        , inj₂
        ]′ (caseHigh-N norm finQ finΓ d' jmax jmax≤cl 1 (fullStates finQ finΓ)
              (s≤s z≤n) (≰⇒> B>P+1) ≤-refl)

pda-pumping-N : {Q T Γ : Set} {M : PDA Q T Γ}
              → IsNormalPDA M → (finQ : Finite Q) (finΓ : Finite Γ)
              → {w : List T} → AccES M w → pumpLen finQ finΓ < length w
              → ∃ λ u → ∃ λ v → ∃ λ x → ∃ λ y → ∃ λ z
                 → w ≡ u ++ v ++ x ++ y ++ z
                 × 0 < length v + length y
                 × (∀ k → AccES M (u ++ rep k v ++ x ++ rep k y ++ z))
pda-pumping-N {M = M} norm finQ finΓ {w} (q_f , d) plen<w =
  pump-run (pumpStep norm finQ finΓ plen<w) d

-- ────────────────────────────────────────────────────────────────
-- THEOREM: the pumping lemma for an arbitrary PDA.
--   Hypothesis: a pushdown automaton M (with Q, T, Γ finite).
--   There is a p such that every word of AccES M longer than p factors
--   as u v x y z with |vy| ≥ 1 and u vᵏ x yᵏ z ∈ AccES M for every k.
--   (FULL language: ε falls under the vacuous case p < |w|.)
-- ────────────────────────────────────────────────────────────────

pumping-pda : {Q T Γ : Set}
              (finQ : Finite Q) (finT : Finite T) (finΓ : Finite Γ)
              (M : PDA Q T Γ)
            → ∃ λ (p : ℕ)
               → ∀ {w : List T} → AccES M w → p < length w
                 → ∃ λ u → ∃ λ v → ∃ λ x → ∃ λ y → ∃ λ z
                    → w ≡ u ++ v ++ x ++ y ++ z
                    × 0 < length v + length y
                    × (∀ k → AccES M (u ++ rep k v ++ x ++ rep k y ++ z))
pumping-pda finQ finT finΓ M =
  let (_ , M′ , M′-norm , finSt′ , sound , complete) = normalize finQ finT finΓ M
  in pumpLen finSt′ (finite-Maybe finΓ)
   , λ {w} accM p<w →
       let (u , v , x , y , z , weq , vy , runs) =
             pda-pumping-N M′-norm finSt′ (finite-Maybe finΓ) (complete w accM) p<w
       in u , v , x , y , z , weq , vy , λ k → sound _ (runs k)
