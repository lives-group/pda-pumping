-- Pumping lemma for an ARBITRARY PDA (the hypothesis is a pushdown
-- automaton; grammars are NEVER mentioned).
--
--   pda-pumping-N : pumping for IsNormalPDA, with |vxy| ≤ p
--                   (the bounded search of PDA.Pumping.Bounded, which
--                   secures |vy| ≥ 1 by well-founded recursion on compLen).
--   pumping-pda   : composes normalize (PDA→IsNormalPDA, full language)
--                   with pda-pumping-N and transports the pumped runs.
module PDA.Pumping.Arbitrary where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; _+_; _<_; _≤_)
open import Data.Product using (∃; ∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import CFG.Base using (Finite)
open import Utils.Finite using (finite-Maybe)
open import PDA.Base using (PDA)
open PDA using (q₀; z₀)
open import PDA.Language using (AccES)
open import PDA.Normal using (IsNormalPDA)
open import PDA.Trace using (rep)
open import PDA.Pumping.Bounded using (pumpBound; module Search)
open import PDA.NormalizePDA using (normalize)

-- ────────────────────────────────────────────────────────────────
-- THEOREM: the pumping lemma for a normal PDA.
--   p = pumpBound = (|Q| + 1) · (pumpLen + 1).
-- ────────────────────────────────────────────────────────────────

pda-pumping-N : {Q T Γ : Set} {M : PDA Q T Γ}
              → IsNormalPDA M → (finQ : Finite Q) (finΓ : Finite Γ)
              → {w : List T} → AccES M w → pumpBound finQ finΓ < length w
              → ∃ λ u → ∃ λ v → ∃ λ x → ∃ λ y → ∃ λ z
                 → w ≡ u ++ v ++ x ++ y ++ z
                 × 0 < length v + length y
                 × length (v ++ x ++ y) ≤ pumpBound finQ finΓ
                 × (∀ k → AccES M (u ++ rep k v ++ x ++ rep k y ++ z))
pda-pumping-N norm finQ finΓ (q_f , d) big
  with Search.bounded-pumping norm finQ finΓ d big
... | u , v , x , y , z , weq , vy , vxy , runs =
  u , v , x , y , z , weq , vy , vxy , λ k → q_f , runs k

-- ────────────────────────────────────────────────────────────────
-- THEOREM: the pumping lemma for an arbitrary PDA.
--   Hypothesis: a pushdown automaton M (with Q, T, Γ finite).
--   There is a p such that every word of AccES M longer than p factors
--   as u v x y z with |vy| ≥ 1, |vxy| ≤ p, and u vᵏ x yᵏ z ∈ AccES M for
--   every k.  (FULL language: ε falls under the vacuous case p < |w|.)
-- ────────────────────────────────────────────────────────────────

pumping-pda : {Q T Γ : Set}
              (finQ : Finite Q) (finT : Finite T) (finΓ : Finite Γ)
              (M : PDA Q T Γ)
            → ∃ λ (p : ℕ)
               → ∀ {w : List T} → AccES M w → p < length w
                 → ∃ λ u → ∃ λ v → ∃ λ x → ∃ λ y → ∃ λ z
                    → w ≡ u ++ v ++ x ++ y ++ z
                    × 0 < length v + length y
                    × length (v ++ x ++ y) ≤ p
                    × (∀ k → AccES M (u ++ rep k v ++ x ++ rep k y ++ z))
pumping-pda finQ finT finΓ M =
  let (_ , M′ , M′-norm , finSt′ , sound , complete) = normalize finQ finT finΓ M
  in pumpBound finSt′ (finite-Maybe finΓ)
   , λ {w} accM p<w →
       let (u , v , x , y , z , weq , vy , vxy , runs) =
             pda-pumping-N M′-norm finSt′ (finite-Maybe finΓ) (complete w accM) p<w
       in u , v , x , y , z , weq , vy , vxy , λ k → sound _ (runs k)
