-- Case 2 of the pumping lemma (level l ≥ p′): the double pump
-- u vⁿ x yⁿ z.  The GEOMETRY (lp/fp/full-state extraction, the
-- frame-polymorphic v/x/y loops, prefix/suffix and factorization) lives in
-- `PDA.Pumping.CaseHighCore`, elaborated once and returned in a
-- `CaseHighData` record.  Here we only wrap that core in the two
-- forms: `caseHigh` (IsNormalPDA⁺, with |vy|≥1 by the balance argument) and
-- `caseHigh-N` (IsNormalPDA, returning EITHER the factorization OR the
-- shorter run at n=0).
module PDA.Pumping.CaseHigh where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Product using (Σ; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; sym; trans; subst)

open import CFG.Base using (Finite; elems)
open import Utils.Finite using (finite-×)
open import PDA.Base using (PDA; _⊢ₚ_⟹*_; compLen)
open import PDA.Normal using (IsNormalPDA⁺; IsNormalPDA; normal⁺⇒normal)
open import PDA.Trace using (rep; sₕ)
open import PDA.Pumping.Shorten using (compLen-substℓ)
open import PDA.Pumping.CaseHighCore using (CaseHighData; caseHigh-core)

-- ────────────────────────────────────────────────────────────────
-- caseHigh: the IsNormalPDA⁺ version.  All the geometry comes from the core;
-- we only ask for |vy|≥1 through the `vy` field (which consumes the stronger hypothesis).
-- ────────────────────────────────────────────────────────────────

caseHigh : {Q T Γ : Set} {M : PDA Q T Γ} {q₀ q_f : Q} {w : List T} {z₀ : Γ}
           (norm⁺ : IsNormalPDA⁺ M) (finQ : Finite Q) (finΓ : Finite Γ)
           (d : M ⊢ₚ (q₀ , w , z₀ ∷ []) ⟹* (q_f , [] , []))
           (j : ℕ) (j≤cl : j ≤ compLen d)
           (g₀ p' : ℕ) → 1 ≤ g₀ → g₀ + p' < sₕ j d
         → length (elems (finite-× finQ (finite-× finΓ finQ))) ≤ p'
         → ∃ λ uw → ∃ λ vw → ∃ λ xw → ∃ λ yw → ∃ λ zw
            → (w ≡ uw ++ vw ++ xw ++ yw ++ zw)
            × (0 < length vw + length yw)
            × (∀ n → M ⊢ₚ (q₀ , uw ++ rep n vw ++ xw ++ rep n yw ++ zw , z₀ ∷ [])
                        ⟹* (q_f , [] , []))
caseHigh norm⁺ finQ finΓ d j j≤cl g₀ p' 1≤g₀ bnd card≤p' =
  uw , vw , xw , yw , zw , wdecomp , vy norm⁺ , dp
  where
    open CaseHighData
      (caseHigh-core (normal⁺⇒normal norm⁺) finQ finΓ d j j≤cl g₀ p' 1≤g₀ bnd card≤p')

-- ────────────────────────────────────────────────────────────────
-- caseHigh-N: the IsNormalPDA version.  In place of |vy|≥1-by-balance, it
-- returns EITHER the factorization (when one of v,y is non-empty) OR the
-- shorter run (double-pump at n=0, whose compLen < compLen d by the core's
-- `cl0<` bound).
-- ────────────────────────────────────────────────────────────────

private
  sumNil : {A : Set} (a b : List A) → (0 < length a + length b) ⊎ (a ≡ [] × b ≡ [])
  sumNil [] [] = inj₂ (refl , refl)
  sumNil [] (_ ∷ _) = inj₁ (s≤s z≤n)
  sumNil (_ ∷ _) b = inj₁ (s≤s z≤n)

caseHigh-N : {Q T Γ : Set} {M : PDA Q T Γ} {q₀ q_f : Q} {w : List T} {z₀ : Γ}
             (norm : IsNormalPDA M) (finQ : Finite Q) (finΓ : Finite Γ)
             (d : M ⊢ₚ (q₀ , w , z₀ ∷ []) ⟹* (q_f , [] , []))
             (j : ℕ) (j≤cl : j ≤ compLen d)
             (g₀ p' : ℕ) → 1 ≤ g₀ → g₀ + p' < sₕ j d
           → length (elems (finite-× finQ (finite-× finΓ finQ))) ≤ p'
           → (∃ λ uw → ∃ λ vw → ∃ λ xw → ∃ λ yw → ∃ λ zw
               → (w ≡ uw ++ vw ++ xw ++ yw ++ zw)
               × (0 < length vw + length yw)
               × (∀ n → M ⊢ₚ (q₀ , uw ++ rep n vw ++ xw ++ rep n yw ++ zw , z₀ ∷ [])
                           ⟹* (q_f , [] , [])))
           ⊎ (∃ λ q' → Σ (M ⊢ₚ (q₀ , w , z₀ ∷ []) ⟹* (q' , [] , []))
                         λ d' → compLen d' < compLen d)
caseHigh-N {M = M} {q₀ = q₀} {q_f = q_f} {w = w} {z₀ = z₀} norm finQ finΓ d j j≤cl g₀ p' 1≤g₀ bnd card≤p' =
  result
  where
    open CaseHighData (caseHigh-core norm finQ finΓ d j j≤cl g₀ p' 1≤g₀ bnd card≤p')

    result : (∃ λ uw₁ → ∃ λ vw₁ → ∃ λ xw₁ → ∃ λ yw₁ → ∃ λ zw₁
                → (w ≡ uw₁ ++ vw₁ ++ xw₁ ++ yw₁ ++ zw₁)
                × (0 < length vw₁ + length yw₁)
                × (∀ n → M ⊢ₚ (q₀ , uw₁ ++ rep n vw₁ ++ xw₁ ++ rep n yw₁ ++ zw₁ , z₀ ∷ [])
                            ⟹* (q_f , [] , [])))
             ⊎ (∃ λ q' → Σ (M ⊢ₚ (q₀ , w , z₀ ∷ []) ⟹* (q' , [] , []))
                           λ d' → compLen d' < compLen d)
    result with sumNil vw yw
    ... | inj₁ pos = inj₁ (uw , vw , xw , yw , zw , wdecomp , pos , dp)
    ... | inj₂ (vw≡[] , yw≡[]) = inj₂ (q_f , shorter , compLen<)
      where
        inputeq0 : w ≡ uw ++ rep 0 vw ++ xw ++ rep 0 yw ++ zw
        inputeq0 = trans wdecomp (cong₂ (λ a b → uw ++ a ++ xw ++ b ++ zw) vw≡[] yw≡[])
        shorter : M ⊢ₚ (q₀ , w , z₀ ∷ []) ⟹* (q_f , [] , [])
        shorter = subst (λ inp → M ⊢ₚ (q₀ , inp , z₀ ∷ []) ⟹* (q_f , [] , [])) (sym inputeq0) (dp 0)
        compLen< : compLen shorter < compLen d
        compLen< = subst (_< compLen d)
                         (sym (compLen-substℓ _ _ (sym inputeq0) (dp 0))) cl0<
