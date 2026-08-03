-- Extremal position locators by height, the basis of lp(h)/fp(h).
--   lastWith  : the last position ≤ bound of height h (maximality).
--   firstWith : the first position in [start, start+steps] of height h (minimality).
-- Existence is a hypothesis, supplied by the discrete IVT (PDA.Pumping.IVT).
module PDA.Pumping.LpFp where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n; _≟_; _≤?_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-irrefl; ≤-antisym; ≤-pred;
                                       ≤∧≢⇒<; <⇒≤; ≰⇒>; ≮⇒≥; m≤n⇒m<n∨m≡n; m≤n⇒m≤1+n; n≤1+n; m≤m+n;
                                       +-identityʳ; +-suc; m+[n∸m]≡n; +-monoʳ-≤; +-monoʳ-<;
                                       +-cancelʳ-≡; m+n∸m≡n; ∸-monoˡ-≤)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

open import CFG.Base using (Finite; elems)
open import Utils.Finite using (finite-×)
open import PDA.Base using (PDA; Config; _⊢ₚ_⟹*_; compLen)
open import PDA.Normal using (IsNormalPDA; IsNormalPDA⁺; normal⁺⇒normal; stkOf)
open import PDA.Trace using (sₕ; stateAt; stackAt; configAt; splitAt; splitAt-compLen;
                              compLen-splitAt-fst; configAt-drop; configAt-take; configAt-segment;
                              bottom-kept)
open import PDA.Pumping.IVT using (ivt)
open import PDA.Pumping.Height using (sₕ-start; sₕ-last)
open import PDA.Pumping.Level using (config-collision-Fin)

-- top of the stack (with a default; used only on non-empty stacks).
headOr : {Γ : Set} → Γ → List Γ → Γ
headOr z [] = z
headOr z (x ∷ _) = x

len0 : {Γ : Set} {xs : List Γ} → length xs ≡ 0 → xs ≡ []
len0 {xs = []} _ = refl
len0 {xs = _ ∷ _} ()

-- ────────────────────────────────────────────────────────────────
-- stackAt-eq: positions of equal height whose height never drops below them
-- in between carry the VERY SAME stack (the bottom is kept by bottom-kept).
-- Dá S_g = stackAt(lp g) = stackAt(fp g) e S_h = stackAt(lp h) = stackAt(fp h).
-- ────────────────────────────────────────────────────────────────

stackAt-eq : {Q T Γ : Set} {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
             (norm : IsNormalPDA M) (d : M ⊢ₚ c₁ ⟹* c₂) (a b : ℕ)
           → a ≤ b → b ≤ compLen d
           → length (stackAt a d) ≡ length (stackAt b d)
           → (∀ p → a ≤ p → p ≤ b → length (stackAt a d) ≤ length (stackAt p d))
           → stackAt a d ≡ stackAt b d
stackAt-eq norm d a b a≤b b≤cl sameHt hgt =
  sym (trans stkb (cong (_++ stackAt a d) α'≡[]))
  where
    dropA = proj₂ (proj₂ (splitAt a d))
    a≤cl : a ≤ compLen d
    a≤cl = ≤-trans a≤b b≤cl
    cl-dropA : a + compLen dropA ≡ compLen d
    cl-dropA = trans (cong (_+ compLen dropA) (sym (compLen-splitAt-fst a d a≤cl)))
                     (splitAt-compLen a d)
    b∸a≤cldA : (b ∸ a) ≤ compLen dropA
    b∸a≤cldA = subst ((b ∸ a) ≤_) (m+n∸m≡n a (compLen dropA))
                     (∸-monoˡ-≤ a (subst (b ≤_) (sym cl-dropA) b≤cl))
    seg = proj₁ (proj₂ (splitAt (b ∸ a) dropA))
    clseg : compLen seg ≡ b ∸ a
    clseg = compLen-splitAt-fst (b ∸ a) dropA b∸a≤cldA
    hyp-seg : ∀ k → k ≤ compLen seg → length (stackAt a d) ≤ length (stkOf (configAt k seg))
    hyp-seg k k≤cs =
      subst (length (stackAt a d) ≤_)
            (sym (cong (λ c → length (stkOf c))
                       (trans (configAt-take (b ∸ a) k dropA k≤b∸a) (configAt-drop a k d))))
            (hgt (a + k) (m≤m+n a k)
                 (subst (a + k ≤_) (m+[n∸m]≡n a≤b) (+-monoʳ-≤ a k≤b∸a)))
      where k≤b∸a : k ≤ b ∸ a
            k≤b∸a = subst (k ≤_) clseg k≤cs
    bk = bottom-kept norm (stackAt a d) {α = []} seg refl hyp-seg
    α' = proj₁ bk
    segEq = proj₂ bk
    segEnd≡b : configAt (b ∸ a) dropA ≡ configAt b d
    segEnd≡b = trans (configAt-drop a (b ∸ a) d) (cong (λ m → configAt m d) (m+[n∸m]≡n a≤b))
    stkb : stackAt b d ≡ α' ++ stackAt a d
    stkb = trans (sym (cong stkOf segEnd≡b)) segEq
    α'≡[] : α' ≡ []
    α'≡[] = len0 (+-cancelʳ-≡ (length (stackAt a d)) (length α') 0 (begin
      length α' + length (stackAt a d)  ≡⟨ sym (length-++ α') ⟩
      length (α' ++ stackAt a d)        ≡⟨ sym (cong length stkb) ⟩
      length (stackAt b d)              ≡⟨ sym sameHt ⟩
      0 + length (stackAt a d)          ∎))

private
  variable
    Q T Γ : Set

-- ────────────────────────────────────────────────────────────────
-- S_h = X ∷ (m'' ++ S_g): the segment v (from S_g to S_h, height ≥ |S_g|)
-- preserves S_g as a suffix (bottom-kept with floor S_g); since |S_g|<|S_h|,
-- the remainder α'' is non-empty and its top is X (= top of S_h = top of S_g).
-- ────────────────────────────────────────────────────────────────

S_h-structure : {M : PDA Q T Γ} {q q' : Q} {w w' : List T} {S_g S_h : List Γ} (z : Γ)
                (norm : IsNormalPDA M)
                (seg : M ⊢ₚ (q , w , S_g) ⟹* (q' , w' , S_h))
              → (∀ k → k ≤ compLen seg → length S_g ≤ length (stkOf (configAt k seg)))
              → length S_g < length S_h
              → headOr z S_g ≡ headOr z S_h
              → ∃ λ m'' → S_h ≡ headOr z S_g ∷ (m'' ++ S_g)
S_h-structure z norm seg flr lt topeq with bottom-kept norm _ {α = []} seg refl flr
... | [] , eq = ⊥-elim (<-irrefl (sym (cong length eq)) lt)
... | a ∷ rest , eq = rest , trans eq (cong (_∷ (rest ++ _)) (sym headEq))
  where headEq = trans topeq (cong (headOr z) eq)

-- ────────────────────────────────────────────────────────────────
-- segment-with-floor: the hypothesis strip needs for the extracted segment
-- seg = take (b∸a) (drop a d) (configAt a d ⟹* configAt b d), a partir
-- from the floor bound on d.  This is what segment-to-loop/strip consume.
-- ────────────────────────────────────────────────────────────────

segment-with-floor : {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
                     (d : M ⊢ₚ c₁ ⟹* c₂) (a b δlen : ℕ) → a ≤ b → b ≤ compLen d
                   → (∀ p → a ≤ p → p < b → δlen < length (stkOf (configAt p d)))
                   → ∀ k → k < compLen (proj₁ (proj₂ (splitAt (b ∸ a) (proj₂ (proj₂ (splitAt a d))))))
                   → δlen < length (stkOf (configAt k (proj₁ (proj₂ (splitAt (b ∸ a) (proj₂ (proj₂ (splitAt a d))))))))
segment-with-floor d a b δlen a≤b b≤cl flr k k<cs =
  subst (δlen <_)
        (sym (cong (λ c → length (stkOf c)) (configAt-segment a (b ∸ a) k d k≤b∸a)))
        (flr (a + k) (m≤m+n a k)
             (subst (a + k <_) (m+[n∸m]≡n a≤b) (+-monoʳ-< a k<b∸a)))
  where
    dropA = proj₂ (proj₂ (splitAt a d))
    a≤cl : a ≤ compLen d
    a≤cl = ≤-trans a≤b b≤cl
    cl-dropA : a + compLen dropA ≡ compLen d
    cl-dropA = trans (cong (_+ compLen dropA) (sym (compLen-splitAt-fst a d a≤cl)))
                     (splitAt-compLen a d)
    b∸a≤cldA : (b ∸ a) ≤ compLen dropA
    b∸a≤cldA = subst ((b ∸ a) ≤_) (m+n∸m≡n a (compLen dropA))
                     (∸-monoˡ-≤ a (subst (b ≤_) (sym cl-dropA) b≤cl))
    k<b∸a : k < b ∸ a
    k<b∸a = subst (k <_) (compLen-splitAt-fst (b ∸ a) dropA b∸a≤cldA) k<cs
    k≤b∸a : k ≤ b ∸ a
    k≤b∸a = <⇒≤ k<b∸a

-- Decomposition of a non-empty stack: xs ≡ (top) ∷ (tail).
uncons : {Γ : Set} (z : Γ) (xs : List Γ) → 0 < length xs
       → ∃ λ t → xs ≡ headOr z xs ∷ t
uncons z [] ()
uncons z (x ∷ t) _ = t , refl

-- The ≤ variant of segment-with-floor (inclusive bound), for bottom-kept.
segment-floor-≤ : {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
                  (d : M ⊢ₚ c₁ ⟹* c₂) (a b δlen : ℕ) → a ≤ b → b ≤ compLen d
                → (∀ p → a ≤ p → p ≤ b → δlen ≤ length (stkOf (configAt p d)))
                → ∀ k → k ≤ compLen (proj₁ (proj₂ (splitAt (b ∸ a) (proj₂ (proj₂ (splitAt a d))))))
                → δlen ≤ length (stkOf (configAt k (proj₁ (proj₂ (splitAt (b ∸ a) (proj₂ (proj₂ (splitAt a d))))))))
segment-floor-≤ d a b δlen a≤b b≤cl flr k k≤cs =
  subst (δlen ≤_)
        (sym (cong (λ c → length (stkOf c)) (configAt-segment a (b ∸ a) k d k≤b∸a)))
        (flr (a + k) (m≤m+n a k)
             (subst (a + k ≤_) (m+[n∸m]≡n a≤b) (+-monoʳ-≤ a k≤b∸a)))
  where
    dropA = proj₂ (proj₂ (splitAt a d))
    a≤cl : a ≤ compLen d
    a≤cl = ≤-trans a≤b b≤cl
    cl-dropA : a + compLen dropA ≡ compLen d
    cl-dropA = trans (cong (_+ compLen dropA) (sym (compLen-splitAt-fst a d a≤cl)))
                     (splitAt-compLen a d)
    b∸a≤cldA : (b ∸ a) ≤ compLen dropA
    b∸a≤cldA = subst ((b ∸ a) ≤_) (m+n∸m≡n a (compLen dropA))
                     (∸-monoˡ-≤ a (subst (b ≤_) (sym cl-dropA) b≤cl))
    k≤b∸a : k ≤ b ∸ a
    k≤b∸a = subst (k ≤_) (compLen-splitAt-fst (b ∸ a) dropA b∸a≤cldA) k≤cs

-- ────────────────────────────────────────────────────────────────
-- lastWith: the greatest position p ≤ bound with sₕ p d ≡ h.
-- ────────────────────────────────────────────────────────────────

lastWith : {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
           (d : M ⊢ₚ c₁ ⟹* c₂) (bound h : ℕ)
         → (∃ λ p → p ≤ bound × sₕ p d ≡ h)
         → ∃ λ p → (p ≤ bound) × (sₕ p d ≡ h)
                 × (∀ q → p < q → q ≤ bound → sₕ q d ≢ h)
lastWith d zero h (p , z≤n , sp) =
  zero , z≤n , sp , λ q 0<q q≤0 _ → ⊥-elim (<-irrefl refl (≤-<-trans q≤0 0<q))
lastWith d (suc b) h ex with sₕ (suc b) d ≟ h
... | yes eq = suc b , ≤-refl , eq ,
               λ q sb<q q≤sb _ → ⊥-elim (<-irrefl refl (≤-<-trans q≤sb sb<q))
... | no ¬eq with ex
... | p , p≤sb , sp = p' , m≤n⇒m≤1+n p'≤b , sp' , maxext
  where
    p≢sb : p ≢ suc b
    p≢sb refl = ¬eq sp
    rec = lastWith d b h (p , ≤-pred (≤∧≢⇒< p≤sb p≢sb) , sp)
    p' = proj₁ rec
    p'≤b = proj₁ (proj₂ rec)
    sp' = proj₁ (proj₂ (proj₂ rec))
    max' = proj₂ (proj₂ (proj₂ rec))
    maxext : ∀ q → p' < q → q ≤ suc b → sₕ q d ≢ h
    maxext q p'<q q≤sb with m≤n⇒m<n∨m≡n q≤sb
    ... | inj₁ q<sb = max' q p'<q (≤-pred q<sb)
    ... | inj₂ refl = ¬eq

-- ────────────────────────────────────────────────────────────────
-- firstWith: the least position p in [start, start+steps] with sₕ p d ≡ h.
-- ────────────────────────────────────────────────────────────────

firstWith : {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
            (d : M ⊢ₚ c₁ ⟹* c₂) (start steps h : ℕ)
          → (∃ λ p → start ≤ p × p ≤ start + steps × sₕ p d ≡ h)
          → ∃ λ p → (start ≤ p) × (p ≤ start + steps) × (sₕ p d ≡ h)
                  × (∀ q → start ≤ q → q < p → sₕ q d ≢ h)
firstWith d start zero h ex with sₕ start d ≟ h
... | yes eq = start , ≤-refl , m≤m+n start zero , eq ,
               λ q s≤q q<s _ → ⊥-elim (<-irrefl refl (≤-<-trans s≤q q<s))
... | no ¬eq with ex
... | p , s≤p , p≤s0 , sp =
        ⊥-elim (¬eq (subst (λ x → sₕ x d ≡ h)
                           (≤-antisym (subst (p ≤_) (+-identityʳ start) p≤s0) s≤p) sp))
firstWith d start (suc s) h ex with sₕ start d ≟ h
... | yes eq = start , ≤-refl , m≤m+n start (suc s) , eq ,
               λ q s≤q q<s _ → ⊥-elim (<-irrefl refl (≤-<-trans s≤q q<s))
... | no ¬eq with ex
... | p , s≤p , p≤ss , sp =
        p' , ≤-trans (n≤1+n start) s1≤p' , subst (p' ≤_) (sym (+-suc start s)) p'≤ , sp' , minext
  where
    s≢p : start ≢ p
    s≢p refl = ¬eq sp
    rec = firstWith d (suc start) s h
            (p , ≤∧≢⇒< s≤p s≢p , subst (p ≤_) (+-suc start s) p≤ss , sp)
    p' = proj₁ rec
    s1≤p' = proj₁ (proj₂ rec)
    p'≤ = proj₁ (proj₂ (proj₂ rec))
    sp' = proj₁ (proj₂ (proj₂ (proj₂ rec)))
    min' = proj₂ (proj₂ (proj₂ (proj₂ rec)))
    minext : ∀ q → start ≤ q → q < p' → sₕ q d ≢ h
    minext q s≤q q<p' with m≤n⇒m<n∨m≡n s≤q
    ... | inj₁ s<q = min' q s<q q<p'
    ... | inj₂ refl = ¬eq

-- ────────────────────────────────────────────────────────────────
-- "Stays above the floor" (no re-crossing): if a has height g, is the last
-- position ≤ j of height g (maxa), and b ≤ j has height h > g, then every
-- position in [a, b] has height ≥ g.
--
-- Proof by contradiction: if sₕ p < g somewhere in [a,b], the IVT on [p, b]
-- (from <g up to h>g) finds q ∈ (a, j] of height g, contradicting maximality of a.
-- ────────────────────────────────────────────────────────────────

above-floor : {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
              (norm : IsNormalPDA M) (d : M ⊢ₚ c₁ ⟹* c₂)
              (j : ℕ) (j≤cl : j ≤ compLen d) (a b g h : ℕ)
            → sₕ a d ≡ g → sₕ b d ≡ h → g < h → b ≤ j
            → (∀ q → a < q → q ≤ j → sₕ q d ≢ g)
            → ∀ p → a ≤ p → p ≤ b → g ≤ sₕ p d
above-floor norm d j j≤cl a b g h sa sb g<h b≤j maxa p a≤p p≤b with sₕ p d ≤? g
... | no ¬sp≤g = <⇒≤ (≰⇒> ¬sp≤g) -- g < sₕ p ⟹ g ≤ sₕ p
... | yes sp≤g with sₕ p d ≟ g
... | yes refl = ≤-refl -- sₕ p ≡ g
... | no sp≢g = ⊥-elim (maxa q a<q (≤-trans q≤b b≤j) sqg)
  where
    sp<g : sₕ p d < g
    sp<g = ≤∧≢⇒< sp≤g sp≢g
    a≢p : a ≢ p
    a≢p refl = <-irrefl refl (subst (_< g) sa sp<g)
    a<p : a < p
    a<p = ≤∧≢⇒< a≤p a≢p
    b≤cl : b ≤ compLen d
    b≤cl = ≤-trans b≤j j≤cl
    exq = ivt norm d p (b ∸ p) (subst (_≤ compLen d) (sym (m+[n∸m]≡n p≤b)) b≤cl) g
            (inj₂ (<⇒≤ sp<g ,
                   subst (g ≤_) (sym (trans (cong (λ x → sₕ x d) (m+[n∸m]≡n p≤b)) sb)) (<⇒≤ g<h)))
    q = proj₁ exq
    a<q : a < q
    a<q = <-≤-trans a<p (proj₁ (proj₂ exq))
    q≤b : q ≤ b
    q≤b = subst (q ≤_) (m+[n∸m]≡n p≤b) (proj₁ (proj₂ (proj₂ exq)))
    sqg : sₕ q d ≡ g
    sqg = proj₂ (proj₂ (proj₂ exq))

-- ────────────────────────────────────────────────────────────────
-- "Stays above the floor", descending side (symmetric to above-floor).
-- a has height h, b ≥ a has height g < h, and b is the first position ≥ j
-- of height g (minb), with j ≤ a.  Then every position in [a,b] has height ≥ g.
-- Proof: if sₕ p < g, the IVT on [a,p] (from h>g down to <g) finds q ∈ [j, b)
-- of height g, contradicting minimality of b.
-- ────────────────────────────────────────────────────────────────

below-floor : {M : PDA Q T Γ} {c₁ c₂ : Config Q T Γ}
              (norm : IsNormalPDA M) (d : M ⊢ₚ c₁ ⟹* c₂)
              (j a b g h : ℕ)
            → sₕ a d ≡ h → sₕ b d ≡ g → g < h → j ≤ a → a ≤ b → b ≤ compLen d
            → (∀ q → j ≤ q → q < b → sₕ q d ≢ g)
            → ∀ p → a ≤ p → p ≤ b → g ≤ sₕ p d
below-floor norm d j a b g h sa sb g<h j≤a a≤b b≤cl minb p a≤p p≤b with sₕ p d ≤? g
... | no ¬sp≤g = <⇒≤ (≰⇒> ¬sp≤g)
... | yes sp≤g with sₕ p d ≟ g
... | yes refl = ≤-refl
... | no sp≢g = ⊥-elim (minb q (≤-trans j≤a a≤q) q<b sqg)
  where
    sp<g : sₕ p d < g
    sp<g = ≤∧≢⇒< sp≤g sp≢g
    p≢b : p ≢ b
    p≢b refl = <-irrefl refl (subst (_< g) sb sp<g)
    p<b : p < b
    p<b = ≤∧≢⇒< p≤b p≢b
    p≤cl : p ≤ compLen d
    p≤cl = ≤-trans p≤b b≤cl
    exq = ivt norm d a (p ∸ a) (subst (_≤ compLen d) (sym (m+[n∸m]≡n a≤p)) p≤cl) g
            (inj₁ (subst (_≤ g) (sym (cong (λ x → sₕ x d) (m+[n∸m]≡n a≤p))) (<⇒≤ sp<g) ,
                   subst (g ≤_) (sym sa) (<⇒≤ g<h)))
    q = proj₁ exq
    a≤q = proj₁ (proj₂ exq)
    q≤p : q ≤ p
    q≤p = subst (q ≤_) (m+[n∸m]≡n a≤p) (proj₁ (proj₂ (proj₂ exq)))
    q<b : q < b
    q<b = ≤-<-trans q≤p p<b
    sqg : sₕ q d ≡ g
    sqg = proj₂ (proj₂ (proj₂ exq))

-- ────────────────────────────────────────────────────────────────
-- lp(h) / fp(h) for a normal accepting computation, around the peak j.
--   lp h : the last position ≤ j of height h  (ascending side).
--   fp h : the first position ≥ j of height h (descending side).
-- Existência via TVI (ivt); extremalidade via lastWith/firstWith.
-- ────────────────────────────────────────────────────────────────

module _ {M : PDA Q T Γ} {q₀ q_f : Q} {w : List T} {z₀ : Γ}
         (norm : IsNormalPDA M)
         (d : M ⊢ₚ (q₀ , w , z₀ ∷ []) ⟹* (q_f , [] , []))
         (j : ℕ) (j≤cl : j ≤ compLen d)
       where

  lp : (h : ℕ) → 1 ≤ h → h ≤ sₕ j d
     → ∃ λ p → (p ≤ j) × (sₕ p d ≡ h) × (∀ q → p < q → q ≤ j → sₕ q d ≢ h)
  lp h 1≤h h≤sj = lastWith d j h existence
    where
      ex = ivt norm d 0 j j≤cl h (inj₂ (subst (_≤ h) (sym (sₕ-start d)) 1≤h , h≤sj))
      existence : ∃ λ p → p ≤ j × sₕ p d ≡ h
      existence = proj₁ ex , proj₁ (proj₂ (proj₂ ex)) , proj₂ (proj₂ (proj₂ ex))

  fp : (h : ℕ) → h ≤ sₕ j d
     → ∃ λ p → (j ≤ p) × (p ≤ compLen d) × (sₕ p d ≡ h)
             × (∀ q → j ≤ q → q < p → sₕ q d ≢ h)
  fp h h≤sj =
    let p , j≤p , p≤ , sp , minp = firstWith d j (compLen d ∸ j) h existence
    in p , j≤p , subst (p ≤_) (m+[n∸m]≡n j≤cl) p≤ , sp , minp
    where
      send : sₕ (j + (compLen d ∸ j)) d ≡ 0
      send = trans (cong (λ x → sₕ x d) (m+[n∸m]≡n j≤cl)) (sₕ-last d)
      ex = ivt norm d j (compLen d ∸ j)
              (subst (_≤ compLen d) (sym (m+[n∸m]≡n j≤cl)) ≤-refl)
              h (inj₁ (subst (_≤ h) (sym send) z≤n , h≤sj))
      existence : ∃ λ p → j ≤ p × p ≤ j + (compLen d ∸ j) × sₕ p d ≡ h
      existence = proj₁ ex , proj₁ (proj₂ ex) , proj₁ (proj₂ (proj₂ ex)) , proj₂ (proj₂ (proj₂ ex))

  -- ────────────────────────────────────────────────────────────────
  -- Monotonicity of lp/fp: since g < h and the path moves ±1 around the
  -- peak j, lp(g) ≤ lp(h) ≤ j ≤ fp(h) ≤ fp(g).  (The IVT finds height h
  -- between pg and j / between j and qg; extremality of ph/qh places it.)
  -- ────────────────────────────────────────────────────────────────
  lp-mono : (g h pg ph : ℕ) → g < h → h ≤ sₕ j d
          → pg ≤ j → sₕ pg d ≡ g
          → ph ≤ j → (∀ q → ph < q → q ≤ j → sₕ q d ≢ h)
          → pg ≤ ph
  lp-mono g h pg ph g<h h≤sj pg≤j spg ph≤j maxph = ≤-trans pg≤q q≤ph
    where
      pgj≤cl : pg + (j ∸ pg) ≤ compLen d
      pgj≤cl = subst (_≤ compLen d) (sym (m+[n∸m]≡n pg≤j)) j≤cl
      exq = ivt norm d pg (j ∸ pg) pgj≤cl h
              (inj₂ (subst (_≤ h) (sym spg) (<⇒≤ g<h) ,
                     subst (h ≤_) (sym (cong (λ x → sₕ x d) (m+[n∸m]≡n pg≤j))) h≤sj))
      q = proj₁ exq
      pg≤q = proj₁ (proj₂ exq)
      q≤j : q ≤ j
      q≤j = subst (q ≤_) (m+[n∸m]≡n pg≤j) (proj₁ (proj₂ (proj₂ exq)))
      sqh : sₕ q d ≡ h
      sqh = proj₂ (proj₂ (proj₂ exq))
      q≤ph : q ≤ ph
      q≤ph = ≮⇒≥ (λ ph<q → maxph q ph<q q≤j sqh)

  fp-mono : (g h qg qh : ℕ) → g < h → h ≤ sₕ j d
          → qg ≤ compLen d → sₕ qg d ≡ g → j ≤ qg
          → j ≤ qh → (∀ q → j ≤ q → q < qh → sₕ q d ≢ h)
          → qh ≤ qg
  fp-mono g h qg qh g<h h≤sj qg≤cl sqg j≤qg j≤qh minqh = ≤-trans qh≤q q≤qg
    where
      jqg≤cl : j + (qg ∸ j) ≤ compLen d
      jqg≤cl = subst (_≤ compLen d) (sym (m+[n∸m]≡n j≤qg)) qg≤cl
      exq = ivt norm d j (qg ∸ j) jqg≤cl h
              (inj₁ (subst (_≤ h) (sym (trans (cong (λ x → sₕ x d) (m+[n∸m]≡n j≤qg)) sqg)) (<⇒≤ g<h) ,
                     h≤sj))
      q = proj₁ exq
      j≤q = proj₁ (proj₂ exq)
      q≤qg : q ≤ qg
      q≤qg = subst (q ≤_) (m+[n∸m]≡n j≤qg) (proj₁ (proj₂ (proj₂ exq)))
      sqh : sₕ q d ≡ h
      sqh = proj₂ (proj₂ (proj₂ exq))
      qh≤q : qh ≤ q
      qh≤q = ≮⇒≥ (λ q<qh → minqh q j≤q q<qh sqh)

  -- ────────────────────────────────────────────────────────────────
  -- Full-state collision: p′+1 heights [g₀ .. g₀+p′] into a type Q×Γ×Q of
  -- size ≤ p′ ⇒ two heights g<h share the same full state
  -- (state at lp, top symbol, state at fp).
  -- ────────────────────────────────────────────────────────────────
  fullstate-collision : (finQ : Finite Q) (finΓ : Finite Γ) (g₀ p' : ℕ)
                      → 1 ≤ g₀ → g₀ + p' < sₕ j d
                      → length (elems (finite-× finQ (finite-× finΓ finQ))) ≤ p'
                      → ∃ λ g → ∃ λ h → ∃ λ pg → ∃ λ ph → ∃ λ qg → ∃ λ qh
                      → (g < h) × (1 ≤ g) × (h < sₕ j d)
                      × ((pg ≤ j) × (sₕ pg d ≡ g) × (∀ q → pg < q → q ≤ j → sₕ q d ≢ g))
                      × ((ph ≤ j) × (sₕ ph d ≡ h) × (∀ q → ph < q → q ≤ j → sₕ q d ≢ h))
                      × ((j ≤ qg) × (qg ≤ compLen d) × (sₕ qg d ≡ g)
                         × (∀ q → j ≤ q → q < qg → sₕ q d ≢ g))
                      × ((j ≤ qh) × (qh ≤ compLen d) × (sₕ qh d ≡ h)
                         × (∀ q → j ≤ q → q < qh → sₕ q d ≢ h))
                      × (stateAt pg d ≡ stateAt ph d)
                      × (headOr z₀ (stackAt pg d) ≡ headOr z₀ (stackAt ph d))
                      × (stateAt qg d ≡ stateAt qh d)
  fullstate-collision finQ finΓ g₀ p' 1≤g₀ bnd card≤p' =
    g , h , proj₁ lpg , proj₁ lph , proj₁ fpg , proj₁ fph , g<h , bnd1 i , h<sj ,
    proj₂ lpg , proj₂ lph , proj₂ fpg , proj₂ fph ,
    cong proj₁ eq , cong (λ t → proj₁ (proj₂ t)) eq , cong (λ t → proj₂ (proj₂ t)) eq
    where
      bnd1 : ∀ k → 1 ≤ g₀ + toℕ k
      bnd1 k = ≤-trans 1≤g₀ (m≤m+n g₀ (toℕ k))
      bndj : ∀ k → g₀ + toℕ k ≤ sₕ j d
      bndj k = ≤-trans (+-monoʳ-≤ g₀ (≤-pred (toℕ<n k))) (<⇒≤ bnd)
      f : Fin (suc p') → Q × Γ × Q
      f k = stateAt (proj₁ (lp (g₀ + toℕ k) (bnd1 k) (bndj k))) d
          , headOr z₀ (stackAt (proj₁ (lp (g₀ + toℕ k) (bnd1 k) (bndj k))) d)
          , stateAt (proj₁ (fp (g₀ + toℕ k) (bndj k))) d
      col = config-collision-Fin (finite-× finQ (finite-× finΓ finQ)) p' f card≤p'
      i = proj₁ col
      i' = proj₁ (proj₂ col)
      i<i' = proj₁ (proj₂ (proj₂ col))
      eq = proj₂ (proj₂ (proj₂ col))
      g = g₀ + toℕ i
      h = g₀ + toℕ i'
      g<h : g < h
      g<h = +-monoʳ-< g₀ i<i'
      h<sj : h < sₕ j d
      h<sj = ≤-<-trans (+-monoʳ-≤ g₀ (≤-pred (toℕ<n i'))) bnd
      lpg = lp g (bnd1 i) (bndj i)
      lph = lp h (bnd1 i') (bndj i')
      fpg = fp g (bndj i)
      fph = fp h (bndj i')

  -- ────────────────────────────────────────────────────────────────
  -- Floor bound through the peak: combines above-floor [pg,j] and
  -- below-floor [j,qg] into a single bound height ≥ lev on [pg, qg].
  -- ────────────────────────────────────────────────────────────────
  floor-through-peak : (lev pg qg : ℕ)
                     → sₕ pg d ≡ lev → sₕ qg d ≡ lev
                     → pg ≤ j → j ≤ qg → qg ≤ compLen d → lev < sₕ j d
                     → (∀ q → pg < q → q ≤ j → sₕ q d ≢ lev)
                     → (∀ q → j ≤ q → q < qg → sₕ q d ≢ lev)
                     → ∀ p → pg ≤ p → p ≤ qg → lev ≤ sₕ p d
  floor-through-peak lev pg qg spg sqg pg≤j j≤qg qg≤cl lev<sj maxpg minqg p pg≤p p≤qg with p ≤? j
  ... | yes p≤j = above-floor norm d j j≤cl pg j lev (sₕ j d) spg refl lev<sj ≤-refl maxpg p pg≤p p≤j
  ... | no ¬p≤j = below-floor norm d j j qg lev (sₕ j d) refl sqg lev<sj ≤-refl j≤qg qg≤cl minqg
                              p (<⇒≤ (≰⇒> ¬p≤j)) p≤qg

  -- ────────────────────────────────────────────────────────────────
  -- Stack equality between positions of equal height lev around the
  -- peak (yields S_g = stackAt(lp g) = stackAt(fp g), likewise S_h).
  -- ────────────────────────────────────────────────────────────────
  stack-eq-peak : (lev pg qg : ℕ)
                → sₕ pg d ≡ lev → sₕ qg d ≡ lev
                → pg ≤ j → j ≤ qg → qg ≤ compLen d → lev < sₕ j d
                → (∀ q → pg < q → q ≤ j → sₕ q d ≢ lev)
                → (∀ q → j ≤ q → q < qg → sₕ q d ≢ lev)
                → stackAt pg d ≡ stackAt qg d
  stack-eq-peak lev pg qg spg sqg pg≤j j≤qg qg≤cl lev<sj maxpg minqg =
    stackAt-eq norm d pg qg (≤-trans pg≤j j≤qg) qg≤cl (trans spg (sym sqg)) hgt
    where
      hgt : ∀ p → pg ≤ p → p ≤ qg → length (stackAt pg d) ≤ length (stackAt p d)
      hgt p pg≤p p≤qg =
        subst (_≤ sₕ p d) (sym spg)
              (floor-through-peak lev pg qg spg sqg pg≤j j≤qg qg≤cl lev<sj maxpg minqg p pg≤p p≤qg)
