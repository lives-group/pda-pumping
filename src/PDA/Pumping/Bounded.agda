-- The bound |vxy| ≤ p, for a normal PDA.
--
-- The search runs on excursions (PDA.Pumping.Excursion).  Let
-- p₀ = pumpLen and K = p₀ + 1.  Given an excursion d reading more than p₀
-- symbols:
--
--   · if it reads at most `bound` = (|Q|+1)·K symbols, the unbounded theorem
--     applied to d itself already gives |vxy| ≤ |consumed d| ≤ bound;
--   · otherwise we walk along its blocks (push X, child excursion of X) at the
--     base level A ∷ [].  If some child reads more than p₀ symbols we
--     recurse into it; if not, every block reads at most K symbols, and
--     among the first |Q|+1 visits of the base level two share a state, so
--     the blocks between them form a loop on an identical configuration
--     reading at most |Q|·K symbols.  A loop that reads nothing is excised,
--     and the search restarts on the strictly shorter excursion.
--
-- The recursion is well-founded on compLen; the walk along the blocks is
-- itself well-founded on the length of the remaining excursion.
module PDA.Pumping.Bounded where

open import Data.Empty using (⊥-elim)
import Data.Fin.Properties as FinP
open import Data.List using (List; []; _∷_; _++_; length; map; lookup)
open import Data.List.Properties using (++-assoc; length-++; length-map; ++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.Any using (index; any?)
open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _≤?_; s≤s; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; <-trans; ≤-reflexive; <-≤-trans; ≰⇒>; <⇒≱; m≤m+n; m≤n+m;
         +-mono-≤; +-monoʳ-<; +-monoˡ-<; +-comm; +-assoc; +-identityʳ; *-monoˡ-≤)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Product using (Σ; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import CFG.Base using (Finite; elems; complete)
open import Utils.AllDistinct using (AllDistinct; []; _∷_; allDistinct-len-bound)
open import PDA.Base
open import PDA.Normal using (IsNormalPDA)
open import PDA.Trace using (consumed; consumed-correct; accepted-word; swap-input; append-stack;
                              loop-rep; rep; compLen-trans)
open import PDA.Pumping.Shorten using (compLen-append)
open import PDA.Pumping.Lemma using (pumpLen; rep-[])
open import PDA.Pumping.Excursion
open import PDA.Pumping.PumpNormal using (pda-pumping-N-at)

-- ────────────────────────────────────────────────────────────────
-- Decidable equality from finiteness (compare positions in the listing)
-- ────────────────────────────────────────────────────────────────

finite-decEq : {A : Set} → Finite A → (x y : A) → Dec (x ≡ y)
finite-decEq fin x y with index (complete fin x) FinP.≟ index (complete fin y)
... | yes eq = yes (trans (lookup-index (complete fin x))
                     (trans (cong (lookup (elems fin)) eq)
                            (sym (lookup-index (complete fin y)))))
... | no neq = no (λ x≡y → neq (cong (λ t → index (complete fin t)) x≡y))

-- ────────────────────────────────────────────────────────────────
-- The bounded pumping statement for an excursion (q , _ , A ∷ []) ⟹* (q_f , _ , [])
-- reading wd.
-- ────────────────────────────────────────────────────────────────

BPump : {Q T Γ : Set} (M : PDA Q T Γ) (q : Q) (A : Γ) (q_f : Q) (wd : List T) (p : ℕ) → Set
BPump M q A q_f wd p = ∃ λ u → ∃ λ v → ∃ λ x → ∃ λ y → ∃ λ z
  → wd ≡ u ++ v ++ x ++ y ++ z
  × 0 < length v + length y
  × length (v ++ x ++ y) ≤ p
  × (∀ k → M ⊢ₚ (q , u ++ rep k v ++ x ++ rep k y ++ z , A ∷ []) ⟹* (q_f , [] , []))

BPump-subst : {Q T Γ : Set} {M : PDA Q T Γ} {q q_f : Q} {A : Γ} {wd wd' : List T} {p : ℕ}
            → wd ≡ wd' → BPump M q A q_f wd p → BPump M q A q_f wd' p
BPump-subst refl b = b

private
  assoc4 : {T : Set} (a b c d E : List T) → (a ++ b ++ c ++ d) ++ E ≡ a ++ b ++ c ++ d ++ E
  assoc4 a b c d E =
    trans (++-assoc a _ E) (cong (a ++_) (trans (++-assoc b _ E) (cong (b ++_) (++-assoc c d E))))

  reassoc : {T : Set} (P u a b c d E : List T)
          → P ++ ((u ++ a ++ b ++ c ++ d) ++ E) ≡ (P ++ u) ++ a ++ b ++ c ++ d ++ E
  reassoc P u a b c d E =
    trans (cong (P ++_) (trans (++-assoc u _ E) (cong (u ++_) (assoc4 a b c d E))))
          (sym (++-assoc P u _))

  factor-len : {T : Set} (u v x y z : List T)
             → length (v ++ x ++ y) ≤ length (u ++ v ++ x ++ y ++ z)
  factor-len u v x y z =
    ≤-trans (≤-trans (m≤m+n (length (v ++ x ++ y)) (length z))
                     (≤-reflexive (trans (sym (length-++ (v ++ x ++ y))) (cong length eq3))))
            (≤-trans (m≤n+m _ (length u)) (≤-reflexive (sym (length-++ u))))
    where
      eq3 : (v ++ x ++ y) ++ z ≡ v ++ x ++ y ++ z
      eq3 = trans (++-assoc v (x ++ y) z) (cong (v ++_) (++-assoc x y z))

  nilOrPos : {T : Set} (xs : List T) → (0 < length xs) ⊎ (xs ≡ [])
  nilOrPos [] = inj₂ refl
  nilOrPos (_ ∷ _) = inj₁ (s≤s z≤n)

-- ────────────────────────────────────────────────────────────────
-- The pumping length of the bounded theorem: (|Q| + 1) · (pumpLen + 1).
-- ────────────────────────────────────────────────────────────────

pumpBound : {Q Γ : Set} → Finite Q → Finite Γ → ℕ
pumpBound finQ finΓ = suc (length (elems finQ)) * suc (pumpLen finQ finΓ)

-- ────────────────────────────────────────────────────────────────
-- The search, for a fixed normal automaton
-- ────────────────────────────────────────────────────────────────

module Search {Q T Γ : Set} {M : PDA Q T Γ} (norm : IsNormalPDA M)
              (finQ : Finite Q) (finΓ : Finite Γ) where

  p₀ : ℕ
  p₀ = pumpLen finQ finΓ

  K : ℕ
  K = suc p₀

  N : ℕ
  N = length (elems finQ)

  bound : ℕ
  bound = pumpBound finQ finΓ

  p₀<bound : p₀ < bound
  p₀<bound = m≤m+n K (N * K)

  -- An excursion that is short already: the unbounded theorem suffices.
  small : {q q_f : Q} {w w_f : List T} {A : Γ}
        → (d : M ⊢ₚ (q , w , A ∷ []) ⟹* (q_f , w_f , []))
        → p₀ < length (consumed d) → length (consumed d) ≤ bound
        → BPump M q A q_f (consumed d) bound
  small d lt le with pda-pumping-N-at norm finQ finΓ (exact d) lt
  ... | u , v , x , y , z , eq , pos , runs =
    u , v , x , y , z , eq , pos
    , ≤-trans (subst (λ t → length (v ++ x ++ y) ≤ length t) (sym eq) (factor-len u v x y z)) le
    , runs

  -- Pumping a child excursion c, in its context (pre, then c over the floor
  -- A ∷ [], then e').
  embed : {q r q₂ q_f : Q} {w w₁ w₂ w_f : List T} {A X : Γ}
        → (pre : M ⊢ₚ (q , w , A ∷ []) ⟹* (r , w₁ , X ∷ A ∷ []))
        → (c : M ⊢ₚ (r , w₁ , X ∷ []) ⟹* (q₂ , w₂ , []))
        → (e' : M ⊢ₚ (q₂ , w₂ , A ∷ []) ⟹* (q_f , w_f , []))
        → BPump M r X q₂ (consumed c) bound
        → BPump M q A q_f (consumed pre ++ consumed c ++ consumed e') bound
  embed {q = q} {q_f = q_f} {A = A} pre c e' (u , v , x , y , z , eq , pos , le , runs) =
      consumed pre ++ u , v , x , y , z ++ consumed e'
    , trans (cong (λ t → consumed pre ++ t ++ consumed e') eq)
            (reassoc (consumed pre) u v x y z (consumed e'))
    , pos , le , run
    where
      run : ∀ k → M ⊢ₚ (q , (consumed pre ++ u) ++ rep k v ++ x ++ rep k y ++ z ++ consumed e'
                         , A ∷ []) ⟹* (q_f , [] , [])
      run k = subst (λ i → M ⊢ₚ (q , i , A ∷ []) ⟹* (q_f , [] , []))
                (reassoc (consumed pre) u (rep k v) x (rep k y) z (consumed e'))
                (⟹*ₚ-trans (swap-input ((u ++ rep k v ++ x ++ rep k y ++ z) ++ consumed e') pre)
                  (⟹*ₚ-trans (append-stack (A ∷ []) (extend-input (runs k) (consumed e')))
                             (exact e')))

  -- Pumping a loop on an identical configuration (x = y = []).
  loopPump : {q s q_f : Q} {w w₁ w₂ w_f : List T} {A : Γ}
           → (pre : M ⊢ₚ (q , w , A ∷ []) ⟹* (s , w₁ , A ∷ []))
           → (mid : M ⊢ₚ (s , w₁ , A ∷ []) ⟹* (s , w₂ , A ∷ []))
           → (e : M ⊢ₚ (s , w₂ , A ∷ []) ⟹* (q_f , w_f , []))
           → 0 < length (consumed mid) → length (consumed mid) ≤ bound
           → BPump M q A q_f (consumed pre ++ consumed mid ++ consumed e) bound
  loopPump {q = q} {q_f = q_f} {A = A} pre mid e pos le =
      consumed pre , consumed mid , [] , [] , consumed e , refl
    , subst (0 <_) (sym (+-identityʳ _)) pos
    , subst (_≤ bound) (sym (cong length (++-identityʳ (consumed mid)))) le
    , run
    where
      run : ∀ k → M ⊢ₚ (q , consumed pre ++ rep k (consumed mid) ++ [] ++ rep k [] ++ consumed e
                         , A ∷ []) ⟹* (q_f , [] , [])
      run k = subst (λ i → M ⊢ₚ (q , consumed pre ++ rep k (consumed mid) ++ i , A ∷ [])
                              ⟹* (q_f , [] , []))
                (sym (cong (_++ consumed e) (rep-[] k)))
                (⟹*ₚ-trans (swap-input (rep k (consumed mid) ++ consumed e) pre)
                  (⟹*ₚ-trans (loop-rep mid k (consumed e)) (exact e)))

  -- The recursion hypothesis: every strictly shorter excursion reading more
  -- than p₀ symbols already pumps within the bound.
  IH : ℕ → Set
  IH m = ∀ {q' q_f' : Q} {w' w_f' : List T} {A' : Γ}
       → (d' : M ⊢ₚ (q' , w' , A' ∷ []) ⟹* (q_f' , w_f' , []))
       → compLen d' < m → p₀ < length (consumed d')
       → BPump M q' A' q_f' (consumed d') bound

  -- A visit of the base level, seen from the current visit (state s, input
  -- w_s, prefix PRE): its state, the prefix up to it, and the segment `mid`
  -- from it to the current visit, which reads at most B symbols.
  record Entry {q s : Q} {w w_s : List T} {A : Γ}
               (PRE : M ⊢ₚ (q , w , A ∷ []) ⟹* (s , w_s , A ∷ [])) (B : ℕ) : Set where
    field
      st  : Q
      win : List T
      pre : M ⊢ₚ (q , w , A ∷ []) ⟹* (st , win , A ∷ [])
      mid : M ⊢ₚ (st , win , A ∷ []) ⟹* (s , w_s , A ∷ [])
      len-eq  : compLen PRE ≡ compLen pre + compLen mid
      mid-pos : 0 < compLen mid
      mid-bnd : length (consumed mid) ≤ B

  open Entry

  extend : {q s s' : Q} {w w_s w_s' : List T} {A : Γ}
           {PRE : M ⊢ₚ (q , w , A ∷ []) ⟹* (s , w_s , A ∷ [])} {B : ℕ}
         → (blk : M ⊢ₚ (s , w_s , A ∷ []) ⟹* (s' , w_s' , A ∷ []))
         → length (consumed blk) ≤ K
         → Entry PRE B → Entry (⟹*ₚ-trans PRE blk) (K + B)
  extend {PRE = PRE} {B} blk le en = record
    { st = st en ; win = win en ; pre = pre en ; mid = ⟹*ₚ-trans (mid en) blk
    ; len-eq = trans (compLen-trans PRE blk)
                 (trans (cong (_+ compLen blk) (len-eq en))
                   (trans (+-assoc (compLen (pre en)) (compLen (mid en)) (compLen blk))
                          (cong (compLen (pre en) +_) (sym (compLen-trans (mid en) blk)))))
    ; mid-pos = subst (0 <_) (sym (compLen-trans (mid en) blk))
                      (≤-trans (mid-pos en) (m≤m+n _ _))
    ; mid-bnd = subst (_≤ K + B)
                  (sym (trans (cong length (consumed-trans (mid en) blk))
                              (length-++ (consumed (mid en)))))
                  (subst (_≤ K + B) (+-comm (length (consumed blk)) (length (consumed (mid en))))
                         (+-mono-≤ le (mid-bnd en)))
    }

  fresh : {q s s' : Q} {w w_s w_s' : List T} {A : Γ}
          (PRE : M ⊢ₚ (q , w , A ∷ []) ⟹* (s , w_s , A ∷ [])) {B : ℕ}
        → (blk : M ⊢ₚ (s , w_s , A ∷ []) ⟹* (s' , w_s' , A ∷ []))
        → 0 < compLen blk → length (consumed blk) ≤ K
        → Entry (⟹*ₚ-trans PRE blk) (K + B)
  fresh {s = s} {w_s = w_s} PRE {B} blk pos le = record
    { st = s ; win = w_s ; pre = PRE ; mid = blk ; len-eq = compLen-trans PRE blk
    ; mid-pos = pos ; mid-bnd = ≤-trans le (m≤m+n K B) }

  st-extend : {q s s' : Q} {w w_s w_s' : List T} {A : Γ}
              {PRE : M ⊢ₚ (q , w , A ∷ []) ⟹* (s , w_s , A ∷ [])} {B : ℕ}
              (blk : M ⊢ₚ (s , w_s , A ∷ []) ⟹* (s' , w_s' , A ∷ [])) (le : length (consumed blk) ≤ K)
            → (hist : List (Entry PRE B)) → map st (map (extend blk le) hist) ≡ map st hist
  st-extend blk le [] = refl
  st-extend blk le (en ∷ h) = cong (st en ∷_) (st-extend blk le h)

  hist-bound : {q s : Q} {w w_s : List T} {A : Γ}
               {PRE : M ⊢ₚ (q , w , A ∷ []) ⟹* (s , w_s , A ∷ [])} {B : ℕ}
             → (hist : List (Entry PRE B)) → AllDistinct (map st hist) → length hist ≤ N
  hist-bound hist dist =
    subst (_≤ N) (length-map st hist)
          (allDistinct-len-bound (finite-decEq finQ) dist (λ y _ → complete finQ y))

  -- A loop that reads nothing is excised: the search restarts on a strictly
  -- shorter excursion of the same word.
  shortcut : {q q_f s : Q} {w w_f w₁ w₂ : List T} {A : Γ}
           → (d : M ⊢ₚ (q , w , A ∷ []) ⟹* (q_f , w_f , []))
           → IH (compLen d) → bound < length (consumed d)
           → (pre : M ⊢ₚ (q , w , A ∷ []) ⟹* (s , w₁ , A ∷ []))
           → (mid : M ⊢ₚ (s , w₁ , A ∷ []) ⟹* (s , w₂ , A ∷ []))
           → (e : M ⊢ₚ (s , w₂ , A ∷ []) ⟹* (q_f , w_f , []))
           → w₁ ≡ w₂
           → compLen d ≡ compLen pre + (compLen mid + compLen e)
           → 0 < compLen mid
           → BPump M q A q_f (consumed d) bound
  shortcut d ih big pre mid e refl cleq pos =
    BPump-subst (consumed-unique d' d)
      (ih d' lt (subst (p₀ <_) (cong length (consumed-unique d d'))
                       (<-trans p₀<bound big)))
    where
      d' = ⟹*ₚ-trans pre e
      lt : compLen d' < compLen d
      lt = subst₂ _<_ (sym (compLen-trans pre e)) (sym cleq)
                  (+-monoʳ-< (compLen pre) (+-monoˡ-< (compLen e) pos))

  -- Two visits of the base level in the same state.
  repeat : {q q_f s t : Q} {w w_f w_s win : List T} {A : Γ}
         → (d : M ⊢ₚ (q , w , A ∷ []) ⟹* (q_f , w_f , []))
         → IH (compLen d) → bound < length (consumed d)
         → (pre : M ⊢ₚ (q , w , A ∷ []) ⟹* (t , win , A ∷ []))
         → (mid : M ⊢ₚ (t , win , A ∷ []) ⟹* (s , w_s , A ∷ []))
         → (e : M ⊢ₚ (s , w_s , A ∷ []) ⟹* (q_f , w_f , []))
         → t ≡ s
         → compLen d ≡ compLen pre + (compLen mid + compLen e)
         → 0 < compLen mid → length (consumed mid) ≤ bound
         → BPump M q A q_f (consumed d) bound
  repeat {w_s = w_s} d ih big pre mid e refl cleq pos le with nilOrPos (consumed mid)
  ... | inj₁ v>0 = BPump-subst (sym wordEq) (loopPump pre mid e v>0 le)
    where
      wordEq : consumed d ≡ consumed pre ++ consumed mid ++ consumed e
      wordEq = trans (consumed-unique d (⟹*ₚ-trans pre (⟹*ₚ-trans mid e)))
                     (trans (consumed-trans pre _) (cong (consumed pre ++_) (consumed-trans mid e)))
  ... | inj₂ v≡[] =
    shortcut d ih big pre mid e (trans (consumed-correct mid) (cong (_++ w_s) v≡[])) cleq pos

  -- The walk along the blocks of the excursion d, at the base level.
  --   PRE  : the prefix of d up to the current visit (state s)
  --   e    : the rest of d
  --   hist : the n earlier visits, in pairwise distinct states
  walk : {q q_f s : Q} {w w_f w_s : List T} {A : Γ}
       → (d : M ⊢ₚ (q , w , A ∷ []) ⟹* (q_f , w_f , []))
       → IH (compLen d) → bound < length (consumed d)
       → (n : ℕ)
       → (PRE : M ⊢ₚ (q , w , A ∷ []) ⟹* (s , w_s , A ∷ []))
       → (e : M ⊢ₚ (s , w_s , A ∷ []) ⟹* (q_f , w_f , []))
       → compLen d ≡ compLen PRE + compLen e
       → length (consumed PRE) ≤ n * K
       → (hist : List (Entry PRE (n * K)))
       → length hist ≡ n
       → AllDistinct (map st hist)
       → Acc _<_ (compLen e)
       → BPump M q A q_f (consumed d) bound
  walk {s = s} d ih big n PRE e cleq preB hist len dist (acc erec)
    with any? (finite-decEq finQ s) (map st hist)
  ... | yes s∈ with ∈-map⁻ st s∈
  ...   | en , _ , s≡ =
          repeat d ih big (pre en) (mid en) e (sym s≡)
            (trans cleq (trans (cong (_+ compLen e) (len-eq en))
                               (+-assoc (compLen (pre en)) (compLen (mid en)) (compLen e))))
            (mid-pos en) (≤-trans (mid-bnd en) nK≤bound)
    where
      n≤N : n ≤ N
      n≤N = subst (_≤ N) len (hist-bound hist dist)
      nK≤bound : n * K ≤ bound
      nK≤bound = ≤-trans (*-monoˡ-≤ K n≤N) (m≤n+m (N * K) K)
  walk {q_f = q_f} {s = s} {w_f = w_f} {w_s = w_s} {A = A}
       d ih big n PRE e cleq preB hist len dist (acc erec)
    | no s∉ with excView norm e
  ... | inj₁ le1 = ⊥-elim (<⇒≱ big wdB)
    where
      n≤N : n ≤ N
      n≤N = subst (_≤ N) len (hist-bound hist dist)
      cdEq : consumed d ≡ consumed PRE ++ consumed e
      cdEq = trans (consumed-unique d (⟹*ₚ-trans PRE e)) (consumed-trans PRE e)
      wdB : length (consumed d) ≤ bound
      wdB = subst (_≤ bound) (sym (trans (cong length cdEq) (length-++ (consumed PRE))))
              (≤-trans (+-mono-≤ (≤-trans preB (*-monoˡ-≤ K n≤N)) (≤-trans le1 (s≤s z≤n)))
                       (≤-reflexive (+-comm (N * K) K)))
  ... | inj₂ (X , r , w₁ , q₂ , w₂ , stp , c , e' , le-st , cl-st , ceq , cleq-e)
    with length (consumed c) ≤? p₀
  ...   | no big-c = BPump-subst (sym wEq) (embed (⟹*ₚ-trans PRE stp) c e' (ih c lt-c (≰⇒> big-c)))
    where
      clE : compLen e ≡ suc (compLen c + compLen e')
      clE = trans cleq-e (cong (_+ (compLen c + compLen e')) cl-st)
      lt-c : compLen c < compLen d
      lt-c = ≤-trans (subst (compLen c <_) (sym clE) (s≤s (m≤m+n (compLen c) (compLen e'))))
                     (subst (compLen e ≤_) (sym cleq) (m≤n+m (compLen e) (compLen PRE)))
      wEq : consumed d ≡ consumed (⟹*ₚ-trans PRE stp) ++ consumed c ++ consumed e'
      wEq = begin
        consumed d                                          ≡⟨ consumed-unique d (⟹*ₚ-trans PRE e) ⟩
        consumed (⟹*ₚ-trans PRE e)                          ≡⟨ consumed-trans PRE e ⟩
        consumed PRE ++ consumed e                          ≡⟨ cong (consumed PRE ++_) ceq ⟩
        consumed PRE ++ consumed stp ++ consumed c ++ consumed e'
                                                            ≡⟨ sym (++-assoc (consumed PRE) _ _) ⟩
        (consumed PRE ++ consumed stp) ++ consumed c ++ consumed e'
                                                            ≡⟨ cong (_++ _) (sym (consumed-trans PRE stp)) ⟩
        consumed (⟹*ₚ-trans PRE stp) ++ consumed c ++ consumed e' ∎
  ...   | yes small-c =
          walk d ih big (suc n) (⟹*ₚ-trans PRE blk) e' cleq' preB' hist' len' dist' (erec lt-e)
    where
      app = append-stack (A ∷ []) c
      blk = ⟹*ₚ-trans stp app
      clE : compLen e ≡ suc (compLen c + compLen e')
      clE = trans cleq-e (cong (_+ (compLen c + compLen e')) cl-st)
      lt-e : compLen e' < compLen e
      lt-e = subst (compLen e' <_) (sym clE) (s≤s (m≤n+m (compLen e') (compLen c)))
      blk-bnd : length (consumed blk) ≤ K
      blk-bnd = subst (_≤ K) (sym (trans (cong length (consumed-trans stp app))
                                         (length-++ (consumed stp))))
                  (+-mono-≤ le-st (subst (_≤ p₀) (sym (cong length (consumed-append (A ∷ []) c)))
                                         small-c))
      blk-pos : 0 < compLen blk
      blk-pos = subst (0 <_) (sym (trans (compLen-trans stp app) (cong (_+ compLen app) cl-st)))
                      (s≤s z≤n)
      cleq' : compLen d ≡ compLen (⟹*ₚ-trans PRE blk) + compLen e'
      cleq' = begin
        compLen d                                                 ≡⟨ cleq ⟩
        compLen PRE + compLen e                                   ≡⟨ cong (compLen PRE +_) cleq-e ⟩
        compLen PRE + (compLen stp + (compLen c + compLen e'))
          ≡⟨ cong (compLen PRE +_) (sym (+-assoc (compLen stp) (compLen c) (compLen e'))) ⟩
        compLen PRE + ((compLen stp + compLen c) + compLen e')
          ≡⟨ sym (+-assoc (compLen PRE) _ (compLen e')) ⟩
        (compLen PRE + (compLen stp + compLen c)) + compLen e'
          ≡⟨ cong (λ t → (compLen PRE + (compLen stp + t)) + compLen e')
                  (sym (compLen-append (A ∷ []) c)) ⟩
        (compLen PRE + (compLen stp + compLen app)) + compLen e'
          ≡⟨ cong (λ t → (compLen PRE + t) + compLen e') (sym (compLen-trans stp app)) ⟩
        (compLen PRE + compLen blk) + compLen e'
          ≡⟨ cong (_+ compLen e') (sym (compLen-trans PRE blk)) ⟩
        compLen (⟹*ₚ-trans PRE blk) + compLen e' ∎
      preB' : length (consumed (⟹*ₚ-trans PRE blk)) ≤ K + n * K
      preB' = subst (_≤ K + n * K)
                (sym (trans (cong length (consumed-trans PRE blk)) (length-++ (consumed PRE))))
                (subst (_≤ K + n * K) (+-comm (length (consumed blk)) (length (consumed PRE)))
                       (+-mono-≤ blk-bnd preB))
      hist' : List (Entry (⟹*ₚ-trans PRE blk) (K + n * K))
      hist' = fresh PRE blk blk-pos blk-bnd ∷ map (extend blk blk-bnd) hist
      len' : length hist' ≡ suc n
      len' = cong suc (trans (length-map (extend blk blk-bnd) hist) len)
      dist' : AllDistinct (map st hist')
      dist' = subst (s ∉_) (sym (st-extend blk blk-bnd hist)) s∉
            ∷ subst AllDistinct (sym (st-extend blk blk-bnd hist)) dist

  find : {q q_f : Q} {w w_f : List T} {A : Γ}
       → (d : M ⊢ₚ (q , w , A ∷ []) ⟹* (q_f , w_f , []))
       → Acc _<_ (compLen d) → p₀ < length (consumed d)
       → BPump M q A q_f (consumed d) bound
  find d (acc rec) lt with length (consumed d) ≤? bound
  ... | yes le = small d lt le
  ... | no gt = walk d (λ d' lt' plt → find d' (rec lt') plt) (≰⇒> gt)
                     zero ε d refl z≤n [] refl [] (<-wellFounded (compLen d))

  -- THEOREM (normal PDA, both endpoints fixed): pumping with |vxy| ≤ bound.
  bounded-pumping : {q q_f : Q} {w : List T} {A : Γ}
                  → (d : M ⊢ₚ (q , w , A ∷ []) ⟹* (q_f , [] , []))
                  → bound < length w
                  → BPump M q A q_f w bound
  bounded-pumping d big =
    BPump-subst (sym (accepted-word d))
      (find d (<-wellFounded _)
            (subst (p₀ <_) (cong length (accepted-word d))
                   (<-trans p₀<bound big)))
