-- Pumping lemma for CFLs via pushdown automata: the DICHOTOMY.
--
-- It joins the two cases into a single theorem `pda-pumping`.  Given an
-- accepting computation `d` of `w` in a normal PDA, let `B = sₕ jmax d` be
-- the peak stack height (via `argmax`) and `P = |Q|²·|Γ|` the number of
-- full states.  The dispatch is on `B ≤? suc P`:
--
--   • B ≤ P+1  →  caseLow  (height bounded by B; #configs ≤ #configs(P+1)
--                 = pumpLen < |w|, so a configuration collision exists).
--   • B > P+1  →  caseHigh (at jmax the stack is high: suc P < B = sₕ jmax d,
--                 which is exactly the strict hypothesis of the high case).
--
-- The pumping constant is `pumpLen = |Q|·(|Γ|+1)^(P+1)`.
module PDA.Pumping.Lemma where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; _≤?_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-<-trans; ≰⇒>; +-identityʳ;
                                       *-monoʳ-≤; ^-monoʳ-≤)
open import Data.Product using (Σ; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

open import CFG.Base using (Finite; elems)
open import Utils.Finite using (finite-×)
open import PDA.Base using (PDA; Config; _⊢ₚ_⟹*_; compLen)
open import PDA.Language using (AccES)
open import PDA.Normal using (IsNormalPDA⁺)
open import PDA.Trace using (rep; sₕ; stackAt)
open import PDA.Pumping.Level using (Cfg; finite-Cfg; card-Cfg)
open import PDA.Pumping.Height using (argmax)
open import PDA.Pumping.CaseLow using (caseLow)
open import PDA.Pumping.CaseHigh using (caseHigh)

-- ────────────────────────────────────────────────────────────────
-- rep n [] ≡ []  (repeating the empty word yields the empty word).
-- ────────────────────────────────────────────────────────────────
rep-[] : {A : Set} (n : ℕ) → rep {A} n [] ≡ []
rep-[] zero = refl
rep-[] (suc n) = rep-[] n

-- ────────────────────────────────────────────────────────────────
-- Monotonicity of #configs in the exponent (the height):
--   a ≤ b → |Cfg a| ≤ |Cfg b|.
-- Via |Cfg l| = |Q|·(|Γ|+1)^l and ^-monoʳ-≤ (base = suc _ ≠ 0).
-- ────────────────────────────────────────────────────────────────
card-Cfg-mono : {Q Γ : Set} (finQ : Finite Q) (finΓ : Finite Γ) {a b : ℕ}
              → a ≤ b
              → length (elems (finite-Cfg finQ finΓ a))
                ≤ length (elems (finite-Cfg finQ finΓ b))
card-Cfg-mono finQ finΓ {a} {b} a≤b =
  subst₂ _≤_ (sym (card-Cfg finQ finΓ a)) (sym (card-Cfg finQ finΓ b))
    (*-monoʳ-≤ (length (elems finQ))
               (^-monoʳ-≤ (suc (length (elems finΓ))) a≤b))

-- ────────────────────────────────────────────────────────────────
-- The pumping constant.
--   P = |Q|²·|Γ| = #full states;   pumpLen = |Cfg (P+1)| = |Q|·(|Γ|+1)^(P+1).
-- ────────────────────────────────────────────────────────────────
fullStates : {Q Γ : Set} → Finite Q → Finite Γ → ℕ
fullStates finQ finΓ = length (elems (finite-× finQ (finite-× finΓ finQ)))

pumpLen : {Q Γ : Set} → Finite Q → Finite Γ → ℕ
pumpLen finQ finΓ =
  length (elems (finite-Cfg finQ finΓ (suc (fullStates finQ finΓ))))

-- ────────────────────────────────────────────────────────────────
-- THEOREM: the pumping lemma (via PDAs).
--
-- For a normal PDA M (in the strong normal form IsNormalPDA⁺), if w is
-- accepted by empty stack and |w| > pumpLen, then w = u v x y z with
-- |vy| ≥ 1 and, for every k, u vᵏ x yᵏ z is accepted.
-- ────────────────────────────────────────────────────────────────
pda-pumping : {Q T Γ : Set} {M : PDA Q T Γ}
              (norm⁺ : IsNormalPDA⁺ M) (finQ : Finite Q) (finΓ : Finite Γ)
              {w : List T}
            → AccES M w
            → pumpLen finQ finΓ < length w
            → ∃ λ u → ∃ λ v → ∃ λ x → ∃ λ y → ∃ λ z
               → w ≡ u ++ v ++ x ++ y ++ z
               × 0 < length v + length y
               × (∀ k → AccES M (u ++ rep k v ++ x ++ rep k y ++ z))
pda-pumping {M = M} norm⁺ finQ finΓ {w} (q_f , d) plen<w
  with argmax d (compLen d)
... | jmax , jmax≤cl , isMax with sₕ jmax d ≤? suc (fullStates finQ finΓ)
... | yes B≤P+1 =
        let (u , v , x , weq , 0<v , run) =
              caseLow norm⁺ finQ finΓ d (sₕ jmax d) isMax
                (≤-<-trans (card-Cfg-mono finQ finΓ B≤P+1) plen<w)
            inputeq : (k : ℕ) → u ++ rep k v ++ x ++ rep k [] ++ [] ≡ u ++ rep k v ++ x
            inputeq k = cong (λ t → u ++ rep k v ++ t)
                          (trans (cong (λ r → x ++ r ++ []) (rep-[] k)) (++-identityʳ x))
        in u , v , x , [] , []
         , trans weq (cong (λ t → u ++ v ++ t) (sym (++-identityʳ x)))
         , subst (0 <_) (sym (+-identityʳ (length v))) 0<v
         , λ k → q_f , subst (λ inp → M ⊢ₚ (_ , inp , _) ⟹* (q_f , [] , []))
                              (sym (inputeq k)) (run k)
... | no B>P+1 =
        let (uw , vw , xw , yw , zw , wdecomp , vy≥1 , run) =
              caseHigh norm⁺ finQ finΓ d jmax jmax≤cl 1 (fullStates finQ finΓ)
                (s≤s z≤n) (≰⇒> B>P+1) ≤-refl
        in uw , vw , xw , yw , zw , wdecomp , vy≥1 , λ k → q_f , run k

-- ────────────────────────────────────────────────────────────────
-- THE PUMPING LEMMA in its usual form (with the length existentially quantified).
--
-- Hypothesis: a pushdown automaton M (with Q and Γ finite, in the strong
-- normal form).  Conclusion: there is a pumping length p such that EVERY
-- word of the language of M (= accepted by empty stack) longer than p
-- factors as u v x y z with |vy| ≥ 1 and u vᵏ x yᵏ z in the language of M
-- for every k.  Grammars are never mentioned: the statement is entirely
-- about the PDA and its language.
-- ────────────────────────────────────────────────────────────────
pumping-lemma : {Q T Γ : Set} (M : PDA Q T Γ)
              → IsNormalPDA⁺ M → Finite Q → Finite Γ
              → ∃ λ (p : ℕ)
                 → ∀ {w : List T}
                   → AccES M w
                   → p < length w
                   → ∃ λ u → ∃ λ v → ∃ λ x → ∃ λ y → ∃ λ z
                      → w ≡ u ++ v ++ x ++ y ++ z
                      × 0 < length v + length y
                      × (∀ k → AccES M (u ++ rep k v ++ x ++ rep k y ++ z))
pumping-lemma M norm⁺ finQ finΓ =
  pumpLen finQ finΓ , λ acc plen<w → pda-pumping norm⁺ finQ finΓ acc plen<w
