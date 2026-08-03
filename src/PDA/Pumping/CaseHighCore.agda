-- Shared core of Case 2 (level l ≥ p′).  The GEOMETRY of the double
-- pump (lp/fp/full-state extraction, the three frame-polymorphic loops
-- (v pushes, x is balanced, y pops), the prefix/suffix and the
-- factorization w = u v x y z) is IDENTICAL in the IsNormalPDA⁺ and
-- IsNormalPDA versions of the case.  Here it is elaborated ONCE and returned
-- in a `CaseHighData` record; `PDA.Pumping.CaseHigh` merely wraps it.
-- (Previously the geometry was duplicated across the two functions of the
-- same module, doubling both the proof term and the type-checking cost.)
module PDA.Pumping.CaseHighCore where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ++-cancelʳ)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≤; <-trans; ≤-<-trans; <-≤-trans;
                                       ≤∧≢⇒<; +-monoʳ-≤; +-monoˡ-≤; +-monoˡ-<;
                                       m≤m+n; m≤n+m; m+[n∸m]≡n; ∸-monoˡ-≤; m+n∸m≡n;
                                       +-assoc; <-irrefl;
                                       +-cancelˡ-<; n<1+n; +-identityʳ)
open import Data.Product using (Σ; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import CFG.Base using (Finite; elems)
open import Utils.Finite using (finite-×)
open import PDA.Base using (PDA; Config; _⊢ₚ_⟹*_; ε; ⟹*ₚ-trans; compLen)
open import PDA.Normal using (IsNormalPDA⁺; IsNormalPDA; normal⁺⇒normal; stkOf)
open import PDA.Trace using (rep; strip; append-stack; swap-input; consumed; consumed-strip; sₕ;
                              splitAt; configAt; stackAt; stateAt; inputAt; stateOf; inputOf;
                              configAt-drop; consumed-window; balance; numEps; compLen-trans;
                              splitAt-compLen; compLen-splitAt-fst)
open import PDA.Pumping.Height using (configAt-last)
open import PDA.Pumping.LpFp using (headOr; fullstate-collision; stack-eq-peak; floor-through-peak;
                                    lp-mono; fp-mono; S_h-structure; segment-with-floor;
                                    segment-floor-≤; uncons)
open import PDA.Pumping.Shorten using (compLen-substℓ; compLen-swap; compLen-append; compLen-strip)

-- rep n w ++ w ≡ w ++ rep n w  (repetition commutes with the suffix).
rep-snoc : {A : Set} (n : ℕ) (w : List A) → rep n w ++ w ≡ w ++ rep n w
rep-snoc zero w = sym (++-identityʳ w)
rep-snoc (suc n) w =
  trans (++-assoc w (rep n w) w) (cong (w ++_) (rep-snoc n w))

-- ────────────────────────────────────────────────────────────────
-- pump-up: repeat n times a loop that pushes m = X ∷ m'' above the top X,
-- keeping X on top.  It reads vⁿ; the stack grows by rep n (X ∷ m'').
-- ────────────────────────────────────────────────────────────────

pump-up : {Q T Γ : Set} {M : PDA Q T Γ} {q : Q} {X : Γ} {m'' : List Γ} {vw : List T}
        → (loop : ∀ {γ : List Γ} {r : List T}
                  → M ⊢ₚ (q , vw ++ r , X ∷ γ) ⟹* (q , r , X ∷ (m'' ++ X ∷ γ)))
        → (n : ℕ) (γ : List Γ) (r : List T)
        → M ⊢ₚ (q , rep n vw ++ r , X ∷ γ) ⟹* (q , r , rep n (X ∷ m'') ++ X ∷ γ)
pump-up loop zero γ r = ε
pump-up {X = X} {m'' = m''} {vw = vw} loop (suc n) γ r
  rewrite ++-assoc vw (rep n vw) r =
  subst (λ s → _ ⊢ₚ (_ , vw ++ rep n vw ++ r , X ∷ γ) ⟹* (_ , r , s)) eq
        (⟹*ₚ-trans (loop {γ} {rep n vw ++ r}) (pump-up loop n (m'' ++ X ∷ γ) r))
  where
    eq : rep n (X ∷ m'') ++ X ∷ (m'' ++ X ∷ γ)
       ≡ rep (suc n) (X ∷ m'') ++ X ∷ γ
    eq = trans (sym (++-assoc (rep n (X ∷ m'')) (X ∷ m'') (X ∷ γ)))
               (cong (_++ X ∷ γ) (rep-snoc n (X ∷ m'')))

-- ────────────────────────────────────────────────────────────────
-- pump-down: the mirror image of pump-up.  Repeat n times a loop that
-- POPS m = X ∷ m'' (reading yw, from X ∷ (m'' ++ X ∷ γ) to X ∷ γ).
-- ────────────────────────────────────────────────────────────────

pump-down : {Q T Γ : Set} {M : PDA Q T Γ} {q : Q} {X : Γ} {m'' : List Γ} {yw : List T}
          → (loop : ∀ {γ : List Γ} {r : List T}
                    → M ⊢ₚ (q , yw ++ r , X ∷ (m'' ++ X ∷ γ)) ⟹* (q , r , X ∷ γ))
          → (n : ℕ) (γ : List Γ) (r : List T)
          → M ⊢ₚ (q , rep n yw ++ r , rep n (X ∷ m'') ++ X ∷ γ) ⟹* (q , r , X ∷ γ)
pump-down loop zero γ r = ε
pump-down {X = X} {m'' = m''} {yw = yw} loop (suc n) γ r
  rewrite trans (cong (_++ r) (sym (rep-snoc n yw))) (++-assoc (rep n yw) yw r)
        | trans (cong (_++ X ∷ γ) (sym (rep-snoc n (X ∷ m''))))
                (++-assoc (rep n (X ∷ m'')) (X ∷ m'') (X ∷ γ)) =
  ⟹*ₚ-trans (pump-down loop n (m'' ++ X ∷ γ) (yw ++ r)) (loop {γ} {r})

-- After n pushes, the stack rep n (X ∷ m'') ++ X ∷ δ begins with X.
rep-X∷ : {Γ : Set} (X : Γ) (m'' δ : List Γ) (n : ℕ)
       → Σ (List Γ) (λ γ → rep n (X ∷ m'') ++ X ∷ δ ≡ X ∷ γ)
rep-X∷ X m'' δ zero = δ , refl
rep-X∷ X m'' δ (suc n) = _ , refl

-- ────────────────────────────────────────────────────────────────
-- double-pump: o GLUING do Caso 2.
-- ────────────────────────────────────────────────────────────────

double-pump : {Q T Γ : Set} {M : PDA Q T Γ}
              {q₀ q_lp q_fp q_f : Q} {X z₀ : Γ} {m'' δ : List Γ}
              {uw vw xw yw zw : List T}
            → (d_u : ∀ {r} → M ⊢ₚ (q₀ , uw ++ r , z₀ ∷ []) ⟹* (q_lp , r , X ∷ δ))
            → (vL : ∀ {γ} {r} → M ⊢ₚ (q_lp , vw ++ r , X ∷ γ) ⟹* (q_lp , r , X ∷ (m'' ++ X ∷ γ)))
            → (xL : ∀ {γ} {r} → M ⊢ₚ (q_lp , xw ++ r , X ∷ γ) ⟹* (q_fp , r , X ∷ γ))
            → (yL : ∀ {γ} {r} → M ⊢ₚ (q_fp , yw ++ r , X ∷ (m'' ++ X ∷ γ)) ⟹* (q_fp , r , X ∷ γ))
            → (d_z : M ⊢ₚ (q_fp , zw , X ∷ δ) ⟹* (q_f , [] , []))
            → (n : ℕ)
            → M ⊢ₚ (q₀ , uw ++ rep n vw ++ xw ++ rep n yw ++ zw , z₀ ∷ [])
                 ⟹* (q_f , [] , [])
double-pump {q_lp = q_lp} {q_fp = q_fp} {X = X} {m'' = m''} {δ = δ}
            {xw = xw} {yw = yw} {zw = zw} d_u vL xL yL d_z n
  with rep-X∷ X m'' δ n
... | γ_n , eq_n =
  ⟹*ₚ-trans d_u
  (⟹*ₚ-trans (pump-up vL n δ (xw ++ rep n yw ++ zw))
  (⟹*ₚ-trans xrun
  (⟹*ₚ-trans (pump-down yL n δ zw) d_z)))
  where
    xrun : _ ⊢ₚ (q_lp , xw ++ rep n yw ++ zw , rep n (X ∷ m'') ++ X ∷ δ)
              ⟹* (q_fp , rep n yw ++ zw , rep n (X ∷ m'') ++ X ∷ δ)
    xrun = subst (λ s → _ ⊢ₚ (q_lp , xw ++ rep n yw ++ zw , s) ⟹* (q_fp , rep n yw ++ zw , s))
                 (sym eq_n) (xL {γ_n} {rep n yw ++ zw})

-- ────────────────────────────────────────────────────────────────
-- dp0-compLen: at n = 0 the loops v,y vanish and double-pump reduces to
-- ⟹*ₚ-trans d_u (⟹*ₚ-trans (xL{δ}) d_z) DEFINITIONALLY.
-- ────────────────────────────────────────────────────────────────

dp0-compLen : {Q T Γ : Set} {M : PDA Q T Γ}
              {q₀ q_lp q_fp q_f : Q} {X z₀ : Γ} {m'' δ : List Γ}
              {uw vw xw yw zw : List T}
            → (d_u : ∀ {r} → M ⊢ₚ (q₀ , uw ++ r , z₀ ∷ []) ⟹* (q_lp , r , X ∷ δ))
            → (vL : ∀ {γ} {r} → M ⊢ₚ (q_lp , vw ++ r , X ∷ γ) ⟹* (q_lp , r , X ∷ (m'' ++ X ∷ γ)))
            → (xL : ∀ {γ} {r} → M ⊢ₚ (q_lp , xw ++ r , X ∷ γ) ⟹* (q_fp , r , X ∷ γ))
            → (yL : ∀ {γ} {r} → M ⊢ₚ (q_fp , yw ++ r , X ∷ (m'' ++ X ∷ γ)) ⟹* (q_fp , r , X ∷ γ))
            → (d_z : M ⊢ₚ (q_fp , zw , X ∷ δ) ⟹* (q_f , [] , []))
            → compLen (double-pump d_u vL xL yL d_z 0)
              ≡ compLen (d_u {xw ++ zw})
              + (compLen (xL {δ} {zw}) + compLen d_z)
dp0-compLen {δ = δ} {xw = xw} {zw = zw} d_u vL xL yL d_z =
  trans (compLen-trans d_u (⟹*ₚ-trans (xL {δ} {zw}) d_z))
        (cong (compLen (d_u {xw ++ zw}) +_) (compLen-trans (xL {δ} {zw}) d_z))

-- ────────────────────────────────────────────────────────────────
-- segment-to-loop: the link between a segment of the run and a
-- frame-polymorphic loop (the hypothesis double-pump expects).
-- ────────────────────────────────────────────────────────────────

segment-to-loop : {Q T Γ : Set} {M : PDA Q T Γ} {q q' : Q}
                  {vw w' : List T} {s S' : List Γ} (α δ : List Γ)
                → (d : M ⊢ₚ (q , vw , s) ⟹* (q' , w' , S'))
                → s ≡ α ++ δ
                → (∀ k → k < compLen d → length δ < sₕ k d)
                → ∃ λ α' → (S' ≡ α' ++ δ)
                         × (∀ {γ : List Γ} {r : List T}
                            → M ⊢ₚ (q , consumed d ++ r , α ++ γ) ⟹* (q' , r , α' ++ γ))
segment-to-loop α δ d seq above = α' , Seq , loop
  where
    str = strip δ {α = α} d seq above
    α' = proj₁ str
    Seq = proj₁ (proj₂ str)
    stripped = proj₂ (proj₂ str)
    loop : ∀ {γ} {r} → _ ⊢ₚ (_ , consumed d ++ r , α ++ γ) ⟹* (_ , r , α' ++ γ)
    loop {γ} {r} = subst (λ inp → _ ⊢ₚ (_ , inp ++ r , α ++ γ) ⟹* (_ , r , α' ++ γ))
                         (consumed-strip δ {α = α} d seq above)
                         (append-stack γ (swap-input r stripped))

-- The loop produced by segment-to-loop has the same compLen as the segment.
segment-to-loop-compLen : {Q T Γ : Set} {M : PDA Q T Γ} {q q' : Q}
                  {vw w' : List T} {s S' : List Γ} (α δ : List Γ)
                → (d : M ⊢ₚ (q , vw , s) ⟹* (q' , w' , S'))
                → (seq : s ≡ α ++ δ)
                → (above : ∀ k → k < compLen d → length δ < sₕ k d)
                → ∀ {γ : List Γ} {r : List T}
                → compLen (proj₂ (proj₂ (segment-to-loop α δ d seq above)) {γ} {r}) ≡ compLen d
segment-to-loop-compLen α δ d seq above {γ} {r} = begin
  compLen (proj₂ (proj₂ (segment-to-loop α δ d seq above)) {γ} {r})
    ≡⟨ compLen-substℓ _ _ (consumed-strip δ {α = α} d seq above)
         (append-stack γ (swap-input r stripped)) ⟩
  compLen (append-stack γ (swap-input r stripped))
    ≡⟨ compLen-append γ (swap-input r stripped) ⟩
  compLen (swap-input r stripped)
    ≡⟨ compLen-swap r stripped ⟩
  compLen stripped
    ≡⟨ compLen-strip δ {α = α} d seq above ⟩
  compLen d ∎
  where
    stripped = proj₂ (proj₂ (strip δ {α = α} d seq above))

-- ────────────────────────────────────────────────────────────────
-- CaseHighData: the result of the shared geometry.  `dp` is the double
-- pump for every n; `cl0<` is the bound compLen(run at n=0) < compLen d
-- (for the well-founded recursion securing |vy|≥1 in the IsNormalPDA case);
-- `vy` delivers |vy|≥1 once the stronger hypothesis IsNormalPDA⁺ is supplied.
-- ────────────────────────────────────────────────────────────────

record CaseHighData {Q T Γ : Set} (M : PDA Q T Γ) (q₀ q_f : Q)
                    (w : List T) (z₀ : Γ)
                    (d : M ⊢ₚ (q₀ , w , z₀ ∷ []) ⟹* (q_f , [] , [])) : Set where
  field
    uw vw xw yw zw : List T
    wdecomp : w ≡ uw ++ vw ++ xw ++ yw ++ zw
    dp : ∀ n → M ⊢ₚ (q₀ , uw ++ rep n vw ++ xw ++ rep n yw ++ zw , z₀ ∷ [])
                  ⟹* (q_f , [] , [])
    cl0< : compLen (dp 0) < compLen d
    vy : IsNormalPDA⁺ M → 0 < length vw + length yw

-- ────────────────────────────────────────────────────────────────
-- caseHigh-core: the assembly of the Case 2 geometry.  It takes the
-- IsNormalPDA hypothesis (enough for all the geometry); the `vy` field is a
-- function taking IsNormalPDA⁺, needed only when |vy|≥1 is required.
-- ────────────────────────────────────────────────────────────────

caseHigh-core-impl : {Q T Γ : Set} {M : PDA Q T Γ} {q₀ q_f : Q} {w : List T} {z₀ : Γ}
           (norm : IsNormalPDA M) (finQ : Finite Q) (finΓ : Finite Γ)
           (d : M ⊢ₚ (q₀ , w , z₀ ∷ []) ⟹* (q_f , [] , []))
           (j : ℕ) (j≤cl : j ≤ compLen d)
           (g₀ p' : ℕ) → 1 ≤ g₀ → g₀ + p' < sₕ j d
         → length (elems (finite-× finQ (finite-× finΓ finQ))) ≤ p'
         → CaseHighData M q₀ q_f w z₀ d
caseHigh-core-impl {M = M} {q₀ = q₀} {q_f = q_f} {w = w} {z₀ = z₀} norm finQ finΓ d j j≤cl g₀ p' 1≤g₀ bnd card≤p'
  with fullstate-collision norm d j j≤cl finQ finΓ g₀ p' 1≤g₀ bnd card≤p'
... | g , h , pg , ph , qg , qh , g<h , 1≤g , h<sj ,
      (pg≤j , spg , maxpg) , (ph≤j , sph , maxph) ,
      (j≤qg , qg≤cl , sqg , minqg) , (j≤qh , qh≤cl , sqh , minqh) ,
      stpgph , toppgph , stqgqh =
      record { uw = uw ; vw = vw ; xw = xw ; yw = yw ; zw = zw
             ; wdecomp = wdecomp
             ; dp = double-pump d_u vL xL yL d_z
             ; cl0< = cl0<
             ; vy = vy }
  where
    gsj : g < sₕ j d
    gsj = <-trans g<h h<sj
    pg≤ph : pg ≤ ph
    pg≤ph = lp-mono norm d j j≤cl g h pg ph g<h (<⇒≤ h<sj) pg≤j spg ph≤j maxph
    qh≤qg : qh ≤ qg
    qh≤qg = fp-mono norm d j j≤cl g h qg qh g<h (<⇒≤ h<sj) qg≤cl sqg j≤qg j≤qh minqh
    ph≤qh : ph ≤ qh
    ph≤qh = ≤-trans ph≤j j≤qh
    pg≤cl : pg ≤ compLen d
    pg≤cl = ≤-trans (≤-trans pg≤j j≤qg) qg≤cl
    ph≤cl : ph ≤ compLen d
    ph≤cl = ≤-trans ph≤qh qh≤cl
    pg≤qh : pg ≤ qh
    pg≤qh = ≤-trans pg≤j j≤qh

    prefix_u = proj₁ (proj₂ (splitAt pg d))
    seg_v = proj₁ (proj₂ (splitAt (ph ∸ pg) (proj₂ (proj₂ (splitAt pg d)))))
    tgt_v = configAt (ph ∸ pg) (proj₂ (proj₂ (splitAt pg d)))
    seg_x = proj₁ (proj₂ (splitAt (qh ∸ ph) (proj₂ (proj₂ (splitAt ph d)))))
    tgt_x = configAt (qh ∸ ph) (proj₂ (proj₂ (splitAt ph d)))
    seg_y = proj₁ (proj₂ (splitAt (qg ∸ qh) (proj₂ (proj₂ (splitAt qh d)))))
    tgt_y = configAt (qg ∸ qh) (proj₂ (proj₂ (splitAt qh d)))
    suffix_z = proj₂ (proj₂ (splitAt qg d))

    tgt_v≡ph : tgt_v ≡ configAt ph d
    tgt_v≡ph = trans (configAt-drop pg (ph ∸ pg) d) (cong (λ m → configAt m d) (m+[n∸m]≡n pg≤ph))
    tgt_x≡qh : tgt_x ≡ configAt qh d
    tgt_x≡qh = trans (configAt-drop ph (qh ∸ ph) d) (cong (λ m → configAt m d) (m+[n∸m]≡n ph≤qh))
    tgt_y≡qg : tgt_y ≡ configAt qg d
    tgt_y≡qg = trans (configAt-drop qh (qg ∸ qh) d) (cong (λ m → configAt m d) (m+[n∸m]≡n qh≤qg))

    uw = consumed prefix_u
    vw = consumed seg_v
    xw = consumed seg_x
    yw = consumed seg_y
    zw = inputAt qg d

    q_lp = stateAt pg d
    q_fp = stateAt qh d

    S_g = stackAt pg d
    Sg≢[] : 0 < length S_g
    Sg≢[] = subst (0 <_) (sym spg) 1≤g
    X = headOr z₀ S_g
    δ_g = proj₁ (uncons z₀ S_g Sg≢[])
    Sg≡Xδg : S_g ≡ X ∷ δ_g
    Sg≡Xδg = proj₂ (uncons z₀ S_g Sg≢[])
    lenδg<g : length δ_g < g
    lenδg<g = subst (length δ_g <_) glen-g (n<1+n (length δ_g))
      where glen-g : suc (length δ_g) ≡ g
            glen-g = trans (sym (cong length Sg≡Xδg)) spg

    ftp-g = floor-through-peak norm d j j≤cl g pg qg spg sqg pg≤j j≤qg qg≤cl gsj maxpg minqg
    ftp-h = floor-through-peak norm d j j≤cl h ph qh sph sqh ph≤j j≤qh qh≤cl h<sj maxph minqh

    stkeq-g : stackAt pg d ≡ stackAt qg d
    stkeq-g = stack-eq-peak norm d j j≤cl g pg qg spg sqg pg≤j j≤qg qg≤cl gsj maxpg minqg
    stkeq-h : stackAt ph d ≡ stackAt qh d
    stkeq-h = stack-eq-peak norm d j j≤cl h ph qh sph sqh ph≤j j≤qh qh≤cl h<sj maxph minqh

    Sh≢[] : 0 < length (stackAt ph d)
    Sh≢[] = subst (0 <_) (sym sph) (≤-trans 1≤g (<⇒≤ g<h))
    Xh = headOr z₀ (stackAt ph d)
    δ_h = proj₁ (uncons z₀ (stackAt ph d) Sh≢[])
    Sh≡Xhδh : stackAt ph d ≡ Xh ∷ δ_h
    Sh≡Xhδh = proj₂ (uncons z₀ (stackAt ph d) Sh≢[])
    lenδh<h : length δ_h < h
    lenδh<h = subst (length δ_h <_) glen-h (n<1+n (length δ_h))
      where glen-h : suc (length δ_h) ≡ h
            glen-h = trans (sym (cong length Sh≡Xhδh)) sph

    Send_v = stkOf tgt_v
    Send_v≡stkph : Send_v ≡ stackAt ph d
    Send_v≡stkph = cong stkOf tgt_v≡ph
    Sh-str = S_h-structure z₀ norm seg_v floor-≤-v lt-v topeq-v
      where
        floor-≤-v = segment-floor-≤ d pg ph (length S_g) pg≤ph ph≤cl
                      (λ p pg≤p p≤ph → subst (_≤ sₕ p d) (sym spg)
                        (ftp-g p pg≤p (≤-trans p≤ph (≤-trans ph≤j j≤qg))))
        lt-v : length S_g < length Send_v
        lt-v = subst (_< length Send_v) (sym spg)
                 (subst (g <_) (sym (trans (cong length Send_v≡stkph) sph)) g<h)
        topeq-v : headOr z₀ S_g ≡ headOr z₀ Send_v
        topeq-v = trans toppgph (sym (cong (headOr z₀) Send_v≡stkph))
    m'' = proj₁ Sh-str
    Send_v≡Xm'' : Send_v ≡ X ∷ (m'' ++ S_g)
    Send_v≡Xm'' = proj₂ Sh-str

    stl-v = segment-to-loop (X ∷ []) δ_g seg_v Sg≡Xδg
              (segment-with-floor d pg ph (length δ_g) pg≤ph ph≤cl
                (λ p pg≤p p<ph → <-≤-trans lenδg<g
                  (ftp-g p pg≤p (≤-trans (<⇒≤ p<ph) (≤-trans ph≤j j≤qg)))))
    α'_v = proj₁ stl-v
    Send_v≡α'v = proj₁ (proj₂ stl-v)
    loop_v = proj₂ (proj₂ stl-v)
    α'v≡ : α'_v ≡ X ∷ (m'' ++ X ∷ [])
    α'v≡ = ++-cancelʳ δ_g α'_v (X ∷ (m'' ++ X ∷ [])) (begin
      α'_v ++ δ_g
        ≡⟨ sym Send_v≡α'v ⟩
      Send_v
        ≡⟨ Send_v≡Xm'' ⟩
      X ∷ (m'' ++ S_g)
        ≡⟨ cong (X ∷_) (trans (cong (m'' ++_) Sg≡Xδg)
                              (sym (++-assoc m'' (X ∷ []) δ_g))) ⟩
      (X ∷ (m'' ++ X ∷ [])) ++ δ_g ∎)
    vL : ∀ {γ} {r} → _ ⊢ₚ (q_lp , vw ++ r , X ∷ γ) ⟹* (q_lp , r , X ∷ (m'' ++ X ∷ γ))
    vL {γ} {r} = subst (λ s → _ ⊢ₚ (q_lp , vw ++ r , X ∷ γ) ⟹* (q_lp , r , s))
                       (trans (cong (_++ γ) α'v≡) (cong (X ∷_) (++-assoc m'' (X ∷ []) γ)))
                   (subst (λ Q → _ ⊢ₚ (q_lp , vw ++ r , X ∷ γ) ⟹* (Q , r , α'_v ++ γ))
                          (trans (cong stateOf tgt_v≡ph) (sym stpgph))
                          (loop_v {γ} {r}))

    stl-x = segment-to-loop (X ∷ []) δ_h seg_x
              (trans Sh≡Xhδh (cong (_∷ δ_h) (sym toppgph)))
              (segment-with-floor d ph qh (length δ_h) ph≤qh qh≤cl
                (λ p ph≤p p<qh → <-≤-trans lenδh<h (ftp-h p ph≤p (<⇒≤ p<qh))))
    α'_x = proj₁ stl-x
    Send_x≡α'x = proj₁ (proj₂ stl-x)
    loop_x = proj₂ (proj₂ stl-x)
    α'x≡ : α'_x ≡ X ∷ []
    α'x≡ = begin
      α'_x     ≡⟨ ++-cancelʳ δ_h α'_x (Xh ∷ []) x-tail ⟩
      Xh ∷ []  ≡⟨ cong (_∷ []) (sym toppgph) ⟩
      X ∷ []   ∎
      where
        x-tail : α'_x ++ δ_h ≡ (Xh ∷ []) ++ δ_h
        x-tail = begin
          α'_x ++ δ_h       ≡⟨ sym Send_x≡α'x ⟩
          stkOf tgt_x       ≡⟨ cong stkOf tgt_x≡qh ⟩
          stackAt qh d      ≡⟨ sym stkeq-h ⟩
          stackAt ph d      ≡⟨ Sh≡Xhδh ⟩
          (Xh ∷ []) ++ δ_h  ∎
    xL : ∀ {γ} {r} → _ ⊢ₚ (q_lp , xw ++ r , X ∷ γ) ⟹* (q_fp , r , X ∷ γ)
    xL {γ} {r} = subst (λ Q → _ ⊢ₚ (Q , xw ++ r , X ∷ γ) ⟹* (q_fp , r , X ∷ γ)) (sym stpgph)
                   (subst (λ s → _ ⊢ₚ (stateAt ph d , xw ++ r , X ∷ γ) ⟹* (q_fp , r , s))
                          (cong (_++ γ) α'x≡)
                     (subst (λ Q → _ ⊢ₚ (stateAt ph d , xw ++ r , X ∷ γ) ⟹* (Q , r , α'_x ++ γ))
                            (cong stateOf tgt_x≡qh)
                            (loop_x {γ} {r})))

    stl-y = segment-to-loop (X ∷ m'') S_g seg_y
              (trans (sym stkeq-h) (trans (sym Send_v≡stkph) Send_v≡Xm''))
              (segment-with-floor d qh qg (length S_g) qh≤qg qg≤cl
                (λ p qh≤p p<qg → subst (_< sₕ p d) (sym spg)
                  (≤∧≢⇒< (ftp-g p (≤-trans pg≤qh qh≤p) (<⇒≤ p<qg))
                         (λ e → minqg p (≤-trans j≤qh qh≤p) p<qg (sym e)))))
    α'_y = proj₁ stl-y
    Send_y≡α'y = proj₁ (proj₂ stl-y)
    loop_y = proj₂ (proj₂ stl-y)
    α'y≡ : α'_y ≡ []
    α'y≡ = ++-cancelʳ S_g α'_y [] (begin
      α'_y ++ S_g   ≡⟨ sym Send_y≡α'y ⟩
      stkOf tgt_y   ≡⟨ cong stkOf tgt_y≡qg ⟩
      stackAt qg d  ≡⟨ sym stkeq-g ⟩
      [] ++ S_g     ∎)
    yL : ∀ {γ} {r} → _ ⊢ₚ (q_fp , yw ++ r , X ∷ (m'' ++ X ∷ γ)) ⟹* (q_fp , r , X ∷ γ)
    yL {γ} {r} = subst (λ s → _ ⊢ₚ (q_fp , yw ++ r , X ∷ (m'' ++ X ∷ γ)) ⟹* (q_fp , r , s))
                       (cong (_++ (X ∷ γ)) α'y≡)
                   (subst (λ Q → _ ⊢ₚ (q_fp , yw ++ r , X ∷ (m'' ++ X ∷ γ)) ⟹* (Q , r , α'_y ++ (X ∷ γ)))
                          (trans (cong stateOf tgt_y≡qg) stqgqh)
                          (loop_y {X ∷ γ} {r}))

    d_u : ∀ {r} → _ ⊢ₚ (q₀ , uw ++ r , z₀ ∷ []) ⟹* (q_lp , r , X ∷ δ_g)
    d_u {r} = subst (λ s → _ ⊢ₚ (q₀ , uw ++ r , z₀ ∷ []) ⟹* (q_lp , r , s))
                    Sg≡Xδg (swap-input r prefix_u)
    d_z : _ ⊢ₚ (q_fp , zw , X ∷ δ_g) ⟹* (q_f , [] , [])
    d_z = subst (λ s → _ ⊢ₚ (q_fp , zw , s) ⟹* (q_f , [] , []))
                (trans (sym stkeq-g) Sg≡Xδg)
            (subst (λ Q → _ ⊢ₚ (Q , zw , stackAt qg d) ⟹* (q_f , [] , [])) stqgqh suffix_z)

    wdecomp : w ≡ uw ++ vw ++ xw ++ yw ++ zw
    wdecomp = trans (consumed-window 0 pg d z≤n pg≤cl)
                (cong (uw ++_) (trans (consumed-window pg ph d pg≤ph ph≤cl)
                  (cong (vw ++_) (trans (consumed-window ph qh d ph≤qh qh≤cl)
                    (cong (xw ++_) (consumed-window qh qg d qh≤qg qg≤cl))))))

    -- the shorter run (n=0) and its compLen bound
    run0 = double-pump d_u vL xL yL d_z 0
    du-cl : compLen (d_u {xw ++ zw}) ≡ pg
    du-cl = begin
      compLen (d_u {xw ++ zw})
        ≡⟨ compLen-substℓ _ _ Sg≡Xδg (swap-input (xw ++ zw) prefix_u) ⟩
      compLen (swap-input (xw ++ zw) prefix_u)
        ≡⟨ compLen-swap (xw ++ zw) prefix_u ⟩
      compLen prefix_u
        ≡⟨ compLen-splitAt-fst pg d pg≤cl ⟩
      pg ∎
    dr_ph = proj₂ (proj₂ (splitAt ph d))
    sumeq_ph : ph + compLen dr_ph ≡ compLen d
    sumeq_ph = trans (cong (_+ compLen dr_ph) (sym (compLen-splitAt-fst ph d ph≤cl)))
                     (splitAt-compLen ph d)
    drge_ph : (qh ∸ ph) ≤ compLen dr_ph
    drge_ph = subst ((qh ∸ ph) ≤_) (m+n∸m≡n ph (compLen dr_ph))
                    (∸-monoˡ-≤ ph (subst (qh ≤_) (sym sumeq_ph) qh≤cl))
    segx-cl : compLen seg_x ≡ qh ∸ ph
    segx-cl = compLen-splitAt-fst (qh ∸ ph) dr_ph drge_ph
    xL-cl : compLen (xL {δ_g} {zw}) ≡ qh ∸ ph
    xL-cl = trans (compLen-substℓ _ _ (sym stpgph) _)
              (trans (compLen-substℓ _ _ (cong (_++ δ_g) α'x≡) _)
                (trans (compLen-substℓ _ _ (cong stateOf tgt_x≡qh) _)
                  (trans (segment-to-loop-compLen (X ∷ []) δ_h seg_x _ _ {δ_g} {zw}) segx-cl)))
    dz-cl : compLen d_z ≡ compLen suffix_z
    dz-cl = trans (compLen-substℓ _ _ (trans (sym stkeq-g) Sg≡Xδg) _)
                  (compLen-substℓ _ _ stqgqh suffix_z)
    dcl : compLen d ≡ qg + compLen suffix_z
    dcl = trans (sym (splitAt-compLen qg d))
                (cong (_+ compLen suffix_z) (compLen-splitAt-fst qg d qg≤cl))
    qh<qg : qh < qg
    qh<qg = ≤∧≢⇒< qh≤qg
              (λ e → <-irrefl (sym (trans (sym sqh) (trans (cong (λ k → sₕ k d) e) sqg))) g<h)
    pgqh<qg : pg + (qh ∸ ph) < qg
    pgqh<qg = ≤-<-trans (subst (pg + (qh ∸ ph) ≤_) (m+[n∸m]≡n ph≤qh)
                               (+-monoˡ-≤ (qh ∸ ph) pg≤ph)) qh<qg
    dp-cl : compLen run0 ≡ (pg + (qh ∸ ph)) + compLen suffix_z
    dp-cl = begin
      compLen run0
        ≡⟨ dp0-compLen d_u vL xL yL d_z ⟩
      compLen (d_u {xw ++ zw}) + (compLen (xL {δ_g} {zw}) + compLen d_z)
        ≡⟨ cong₂ _+_ du-cl (cong₂ _+_ xL-cl dz-cl) ⟩
      pg + ((qh ∸ ph) + compLen suffix_z)
        ≡⟨ sym (+-assoc pg (qh ∸ ph) (compLen suffix_z)) ⟩
      (pg + (qh ∸ ph)) + compLen suffix_z ∎
    cl0< : compLen run0 < compLen d
    cl0< = subst₂ _<_ (sym dp-cl) (sym dcl) (+-monoˡ-< (compLen suffix_z) pgqh<qg)

    -- |vy| ≥ 1 (only under IsNormalPDA⁺): the segment y descends from h to g.
    vy : IsNormalPDA⁺ M → 0 < length vw + length yw
    vy norm⁺ = <-≤-trans 0<yw (m≤n+m (length yw) (length vw))
      where
        sₕend-y : sₕ (compLen seg_y) seg_y ≡ g
        sₕend-y = trans (cong (λ c → length (stkOf c))
                              (trans (configAt-last seg_y) tgt_y≡qg)) sqg
        bal : sₕ (compLen seg_y) seg_y + length yw ≡ h + numEps seg_y
        bal = trans (sym (balance norm⁺ seg_y)) (cong (_+ numEps seg_y) sqh)
        g<g+yw : g < g + length yw
        g<g+yw = subst (g <_)
                   (trans (sym bal) (cong (_+ length yw) sₕend-y))
                   (<-≤-trans g<h (m≤m+n h (numEps seg_y)))
        0<yw : 0 < length yw
        0<yw = +-cancelˡ-< g 0 (length yw)
                 (subst (_< g + length yw) (sym (+-identityʳ g)) g<g+yw)

-- ────────────────────────────────────────────────────────────────
-- caseHigh-core: an OPAQUE façade over the core.  Without `opaque`,
-- consumers (PDA.Pumping.CaseHigh and beyond) would try to REDUCE
-- `caseHigh-core args` to a `record{…}` in order to project each field,
-- replicating the >9min of geometry in EVERY consumer.  Sealed, the
-- projection is inert (like a postulate) and only the record's TYPE is
-- used; the wrappers check in seconds again.
-- ────────────────────────────────────────────────────────────────
opaque
  caseHigh-core : {Q T Γ : Set} {M : PDA Q T Γ} {q₀ q_f : Q} {w : List T} {z₀ : Γ}
             (norm : IsNormalPDA M) (finQ : Finite Q) (finΓ : Finite Γ)
             (d : M ⊢ₚ (q₀ , w , z₀ ∷ []) ⟹* (q_f , [] , []))
             (j : ℕ) (j≤cl : j ≤ compLen d)
             (g₀ p' : ℕ) → 1 ≤ g₀ → g₀ + p' < sₕ j d
           → length (elems (finite-× finQ (finite-× finΓ finQ))) ≤ p'
           → CaseHighData M q₀ q_f w z₀ d
  caseHigh-core = caseHigh-core-impl
