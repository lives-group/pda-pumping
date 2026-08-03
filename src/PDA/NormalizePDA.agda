-- Normalization of an ARBITRARY PDA into the ±1 normal form (IsNormalPDA),
-- preserving the language (acceptance by empty stack), ε included.
--
-- Scheme (it mirrors PDA.NormalForm, but starts from the transitions of M,
-- not from a grammar):
--   · Γ' = Maybe Γ;  nothing = ⊥ is the bottom marker (z₀'),  just A = an
--     original symbol.  The stack of M', simulating M with stack s, is  map just s ++ ⊥ ∷ [].
--   · every move (r,β) ∈ δ q mt A becomes: pop A (reading mt, or an ε-step)
--     and push β symbol by symbol through ε-steps (each one restores the top).
--   · once ⊥ is exposed (the stack of M is empty), an ε-pop of ⊥ empties the
--     stack of M' and it accepts.  Since an ε-pop is allowed in IsNormalPDA (not in ⁺), ε is accepted.
module PDA.NormalizePDA where

open import Data.Bool using (Bool; false)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (n<1+n; ≤-refl)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; drop; take; reverse; map)
open import Data.List.Properties using (unfold-reverse; map-++; ++-assoc;
                                        reverse-involutive; length-reverse;
                                        take-suc; take-all; reverse-++)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (Any; here; there; index)
open import Data.List.Relation.Unary.Any.Properties using (lookup-index) renaming (map⁺ to Any-map⁺)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import CFG.Base using (Finite; DecEq; elems)
open import Utils.Finite using (finite-Σ; finite-Fin; finite-⊎; finite-Maybe)
open import PDA.Base using (PDA; Config; _⊢ₚ_⟹_; _⊢ₚ_⟹*_; ε; _◅_; read; eps; ⟹*ₚ-trans)
open PDA using (δ; q₀; z₀)
open import PDA.Language using (AccES)
open import PDA.Normal using (IsNormalPDA)
open import Utils.Maybe using (just-inj; map-just; map-nothing)
open import Utils.Nat using (∸-suc-lemma)
open import Utils.Fin
  using (allFins; finSucc?; fin0?; finSucc?-just; finSucc?-last; finSucc?-spec;
         drop-at-lookup; drop-all; len0; fin0?-zero; fin0?-sucL; fin0?-fzero)

module _ {Q T Γ : Set}
         (finQ : Finite Q) (finT : Finite T) (finΓ : Finite Γ)
         (M : PDA Q T Γ)
       where

 -- ────────────────────────────────────────────────────────────────
 -- Identidade de transições de M e sequência de empilhamento
 -- ────────────────────────────────────────────────────────────────

 -- One move of M: state q, read mt, top symbol A, index into the list δ q mt A.
 Move : Set
 Move = Σ Q (λ q → Σ (Maybe T) (λ mt → Σ Γ (λ A → Fin (length (M .δ q mt A)))))

 tgt : Move → Q
 tgt (q , mt , A , i) = proj₁ (lookup (M .δ q mt A) i)

 rhs : Move → List Γ
 rhs (q , mt , A , i) = proj₂ (lookup (M .δ q mt A) i)

 -- Push order: reverse β, so that β[0] ends up on top.
 pushβ : Move → List Γ
 pushβ m = reverse (rhs m)

 PushSt : Set
 PushSt = Σ Move (λ m → Fin (length (pushβ m)))

 -- The states of M':
 --   inj₁ (just q)        Sim q   : simulating M in state q
 --   inj₁ nothing         Init    : the initial state (pushes z₀ over ⊥)
 --   inj₂ (inj₁ m)        Strt m  : begins pushing pushβ m (no index yet)
 --   inj₂ (inj₂ (m , j))  Psh m j : pushing pushβ m at position j
 State : Set
 State = Maybe Q ⊎ (Move ⊎ PushSt)

 Sim : Q → State
 Sim q = inj₁ (just q)

 Init : State
 Init = inj₁ nothing

 Strt : Move → State
 Strt m = inj₂ (inj₁ m)

 Psh : (m : Move) → Fin (length (pushβ m)) → State
 Psh m j = inj₂ (inj₂ (m , j))

 -- ────────────────────────────────────────────────────────────────
 -- Finitude
 -- ────────────────────────────────────────────────────────────────

 finite-Move : Finite Move
 finite-Move = finite-Σ finQ (λ q → finite-Σ (finite-Maybe finT)
                 (λ mt → finite-Σ finΓ (λ A → finite-Fin (length (M .δ q mt A)))))

 finite-PushSt : Finite PushSt
 finite-PushSt = finite-Σ finite-Move (λ m → finite-Fin (length (pushβ m)))

 finite-State : Finite State
 finite-State = finite-⊎ (finite-Maybe finQ) (finite-⊎ finite-Move finite-PushSt)

 -- ────────────────────────────────────────────────────────────────
 -- Auxiliares de Fin (espelham PDA.NormalForm)
 -- ────────────────────────────────────────────────────────────────


 -- ────────────────────────────────────────────────────────────────
 -- Função de transição
 -- ────────────────────────────────────────────────────────────────

 -- Alvo após desempilhar A: Sim (tgt m) se β vazio; senão StartPush.
 -- Ramifica em length (pushβ m) (ℕ, sem índice) — como theNextStateV.
 popTargetV : Move → ℕ → State
 popTargetV m zero = Sim (tgt m)
 popTargetV m (suc _) = Strt m

 popTarget : Move → State
 popTarget m = popTargetV m (length (pushβ m))

 -- Sim q, reading mt, with A on top: for each move (index i) it pops A (β=[])
 -- and goes to popTarget.
 popList : (q : Q) (mt : Maybe T) (A : Γ) → List (State × List (Maybe Γ))
 popList q mt A =
   map (λ i → (popTarget (q , mt , A , i) , [])) (allFins (length (M .δ q mt A)))

 -- Push (m,j) on ε, with Z on top: pushes pushβ[j] restoring Z; then advances or stops.
 pushMove : (m : Move) (j : Fin (length (pushβ m))) (Z : Maybe Γ)
          → List (State × List (Maybe Γ))
 pushMove m j Z with finSucc? j
 ... | just j′ = (Psh m j′ , just (lookup (pushβ m) j) ∷ Z ∷ []) ∷ []
 ... | nothing = (Sim (tgt m) , just (lookup (pushβ m) j) ∷ Z ∷ []) ∷ []

 -- Strt m on ε, with Z on top: performs the push at position 0.
 startPushMove : (m : Move) (Z : Maybe Γ) → List (State × List (Maybe Γ))
 startPushMove m Z with fin0? (length (pushβ m))
 ... | just j = pushMove m j Z
 ... | nothing = []

 δ′ : State → Maybe T → Maybe Γ → List (State × List (Maybe Γ))
 -- Init: pushes z₀ over ⊥.
 δ′ (inj₁ nothing) nothing nothing = (Sim (M .q₀) , just (M .z₀) ∷ nothing ∷ []) ∷ []
 δ′ (inj₁ nothing) nothing (just _) = []
 δ′ (inj₁ nothing) (just _) _ = []
 -- Sim q: pops the top according to a move of M; ⊥ ⇒ accept (ε-pop).
 δ′ (inj₁ (just q)) (just a) (just A) = popList q (just a) A
 δ′ (inj₁ (just q)) (just _) nothing = []
 δ′ (inj₁ (just q)) nothing (just A) = popList q nothing A
 δ′ (inj₁ (just q)) nothing nothing = (Sim q , []) ∷ []
 -- Strt m / Psh m j: empilham (somente ε).
 δ′ (inj₂ (inj₁ m)) (just _) _ = []
 δ′ (inj₂ (inj₁ m)) nothing Z = startPushMove m Z
 δ′ (inj₂ (inj₂ (m , j))) (just _) _ = []
 δ′ (inj₂ (inj₂ (m , j))) nothing Z = pushMove m j Z

 -- The normalized PDA, under empty-stack acceptance.
 M′ : PDA State T (Maybe Γ)
 M′ = record { δ = δ′ ; q₀ = Init ; z₀ = nothing ; isFinal = λ _ → false }

 -- ────────────────────────────────────────────────────────────────
 -- M′ is IsNormalPDA (every step is a pop β≡[] or a push β≡X∷Z∷[])
 -- ────────────────────────────────────────────────────────────────

 popList-β : (q : Q) (mt : Maybe T) (A : Γ)
           → ∀ {r β} → (r , β) ∈ popList q mt A → β ≡ []
 popList-β q mt A mem with ∈-map⁻ _ mem
 ... | i , _ , refl = refl

 pushMove-β : (m : Move) (j : Fin (length (pushβ m))) (Z : Maybe Γ)
            → ∀ {r β} → (r , β) ∈ pushMove m j Z
            → ∃ λ X → β ≡ X ∷ Z ∷ []
 pushMove-β m j Z mem with finSucc? j
 pushMove-β m j Z (here refl) | just j′ = just (lookup (pushβ m) j) , refl
 pushMove-β m j Z (there ()) | just j′
 pushMove-β m j Z (here refl) | nothing = just (lookup (pushβ m) j) , refl
 pushMove-β m j Z (there ()) | nothing

 startPushMove-β : (m : Move) (Z : Maybe Γ)
                 → ∀ {r β} → (r , β) ∈ startPushMove m Z
                 → ∃ λ X → β ≡ X ∷ Z ∷ []
 startPushMove-β m Z mem with fin0? (length (pushβ m))
 ... | just j = pushMove-β m j Z mem
 startPushMove-β m Z () | nothing

 M′-normal : IsNormalPDA M′
 M′-normal (inj₁ nothing) nothing nothing (here refl) =
   inj₂ (just (M .z₀) , refl)
 M′-normal (inj₁ nothing) nothing nothing (there ())
 M′-normal (inj₁ (just q)) (just a) (just A) mem = inj₁ (popList-β q (just a) A mem)
 M′-normal (inj₁ (just q)) nothing (just A) mem = inj₁ (popList-β q nothing A mem)
 M′-normal (inj₁ (just q)) nothing nothing (here refl) = inj₁ refl
 M′-normal (inj₁ (just q)) nothing nothing (there ())
 M′-normal (inj₂ (inj₁ m)) nothing Z mem = inj₂ (startPushMove-β m Z mem)
 M′-normal (inj₂ (inj₂ (m , j))) nothing Z mem = inj₂ (pushMove-β m j Z mem)

 -- ════════════════════════════════════════════════════════════════
 -- COMPLETUDE: AccES M w → AccES M′ w   (camada 1: empilhamento)
 -- ════════════════════════════════════════════════════════════════


 pushMove-nothing : (m : Move) (j : Fin (length (pushβ m))) (Z : Maybe Γ) → finSucc? j ≡ nothing
                  → pushMove m j Z ≡ (Sim (tgt m) , just (lookup (pushβ m) j) ∷ Z ∷ []) ∷ []
 pushMove-nothing m j Z eqN rewrite eqN = refl

 pushMove-just : (m : Move) (j j′ : Fin (length (pushβ m))) (Z : Maybe Γ) → finSucc? j ≡ just j′
               → pushMove m j Z ≡ (Psh m j′ , just (lookup (pushβ m) j) ∷ Z ∷ []) ∷ []
 pushMove-just m j j′ Z eqJ rewrite eqJ = refl

 -- pushedβ m j = the pushed stack (just-wrapped) from position j onwards.
 pushedβ : (m : Move) → Fin (length (pushβ m)) → List (Maybe Γ)
 pushedβ m j = map just (reverse (drop (toℕ j) (pushβ m)))

 -- From q (whose ε-transition with Z′ on top is pushMove m j Z′), the ε-steps
 -- push pushβ[j..] (wrapped) and land in Sim (tgt m).
 push-iter : (m : Move) (j : Fin (length (pushβ m))) (q : State)
             (w : List T) (Z : Maybe Γ) (γ : List (Maybe Γ))
           → (∀ Z′ → δ′ q nothing Z′ ≡ pushMove m j Z′)
           → Acc _<_ (length (pushβ m) ∸ toℕ j)
           → M′ ⊢ₚ (q , w , Z ∷ γ) ⟹* (Sim (tgt m) , w , pushedβ m j ++ Z ∷ γ)
 push-iter m j q w Z γ heq (acc rs) with finSucc?-spec j
 ... | inj₁ (eqN , lastpf) =
       subst (λ s → M′ ⊢ₚ (q , w , Z ∷ γ) ⟹* (Sim (tgt m) , w , s ++ Z ∷ γ))
             stk-eq (eps mem ◅ ε)
   where
     mem : (Sim (tgt m) , just (lookup (pushβ m) j) ∷ Z ∷ []) ∈ δ′ q nothing Z
     mem = subst (λ L → (Sim (tgt m) , just (lookup (pushβ m) j) ∷ Z ∷ []) ∈ L)
                 (sym (trans (heq Z) (pushMove-nothing m j Z eqN))) (here refl)
     dl : drop (toℕ j) (pushβ m) ≡ lookup (pushβ m) j ∷ []
     dl = trans (drop-at-lookup (pushβ m) j)
                (cong (lookup (pushβ m) j ∷_)
                      (trans (cong (λ k → drop k (pushβ m)) lastpf) (drop-all (pushβ m))))
     stk-eq : just (lookup (pushβ m) j) ∷ [] ≡ pushedβ m j
     stk-eq = sym (cong (map just) (trans (cong reverse dl)
                                          (unfold-reverse (lookup (pushβ m) j) [])))
 ... | inj₂ (j′ , eqJ , tj′) =
       subst (λ s → M′ ⊢ₚ (q , w , Z ∷ γ) ⟹* (Sim (tgt m) , w , s))
             stk-eq
             (eps mem
              ◅ push-iter m j′ (Psh m j′) w (just (lookup (pushβ m) j)) (Z ∷ γ)
                          (λ _ → refl) (rs meas))
   where
     mem : (Psh m j′ , just (lookup (pushβ m) j) ∷ Z ∷ []) ∈ δ′ q nothing Z
     mem = subst (λ L → (Psh m j′ , just (lookup (pushβ m) j) ∷ Z ∷ []) ∈ L)
                 (sym (trans (heq Z) (pushMove-just m j j′ Z eqJ))) (here refl)
     meas : length (pushβ m) ∸ toℕ j′ < length (pushβ m) ∸ toℕ j
     meas = subst (λ x → length (pushβ m) ∸ x < length (pushβ m) ∸ toℕ j) (sym tj′)
                  (subst (λ y → length (pushβ m) ∸ suc (toℕ j) < y)
                         (sym (∸-suc-lemma (toℕ j) (length (pushβ m)) (toℕ<n j)))
                         (n<1+n _))
     dl : drop (toℕ j) (pushβ m) ≡ lookup (pushβ m) j ∷ drop (toℕ j′) (pushβ m)
     dl = trans (drop-at-lookup (pushβ m) j)
                (cong (λ k → lookup (pushβ m) j ∷ drop k (pushβ m)) (sym tj′))
     pushedβ-eq : pushedβ m j ≡ pushedβ m j′ ++ (just (lookup (pushβ m) j) ∷ [])
     pushedβ-eq = trans (cong (map just) (trans (cong reverse dl)
                          (unfold-reverse (lookup (pushβ m) j) (drop (toℕ j′) (pushβ m)))))
                        (map-++ just (reverse (drop (toℕ j′) (pushβ m)))
                                     (lookup (pushβ m) j ∷ []))
     stk-eq : pushedβ m j′ ++ (just (lookup (pushβ m) j) ∷ Z ∷ γ) ≡ pushedβ m j ++ Z ∷ γ
     stk-eq = sym (trans (cong (_++ Z ∷ γ) pushedβ-eq)
                         (++-assoc (pushedβ m j′) (just (lookup (pushβ m) j) ∷ []) (Z ∷ γ)))

 startPushMove-eq : (m : Move) (j : Fin (length (pushβ m))) (Z : Maybe Γ)
                  → fin0? (length (pushβ m)) ≡ just j
                  → startPushMove m Z ≡ pushMove m j Z
 startPushMove-eq m j Z eqF rewrite eqF = refl

 startPush-iter : (m : Move) (j : Fin (length (pushβ m)))
                  (w : List T) (Z : Maybe Γ) (γ : List (Maybe Γ))
                → fin0? (length (pushβ m)) ≡ just j
                → Acc _<_ (length (pushβ m) ∸ toℕ j)
                → M′ ⊢ₚ (Strt m , w , Z ∷ γ) ⟹* (Sim (tgt m) , w , pushedβ m j ++ Z ∷ γ)
 startPush-iter m j w Z γ eqF acP =
   push-iter m j (Strt m) w Z γ (λ Z′ → startPushMove-eq m j Z′ eqF) acP

 -- ── layer 2: membership + the macro of one move of M ──

 anyAllFins : ∀ {n} {P : Fin n → Set} (i : Fin n) → P i → Any P (allFins n)
 anyAllFins fzero pi = here pi
 anyAllFins (fsuc i) pi = there (Any-map⁺ (anyAllFins i pi))


 popTargetV-ready : (m : Move) → length (pushβ m) ≡ zero → popTarget m ≡ Sim (tgt m)
 popTargetV-ready m eq = cong (popTargetV m) eq

 popTargetV-start : (m : Move) {n : ℕ} → length (pushβ m) ≡ suc n → popTarget m ≡ Strt m
 popTargetV-start m eq = cong (popTargetV m) eq

 -- Encoding the stack of M into that of M′:  enc s = map just s ++ ⊥ ∷ [].
 enc : List Γ → List (Maybe Γ)
 enc s = map just s ++ nothing ∷ []

 enc-cons : (s : List Γ) → ∃ λ Z → ∃ λ γ → enc s ≡ Z ∷ γ
 enc-cons [] = nothing , [] , refl
 enc-cons (x ∷ s) = just x , enc s , refl

 -- From popTarget m, pushes map just (rhs m) (leaving β on top, wrapped).
 push-all : (m : Move) (w : List T) (Z : Maybe Γ) (γ : List (Maybe Γ))
          → M′ ⊢ₚ (popTarget m , w , Z ∷ γ)
                 ⟹* (Sim (tgt m) , w , map just (rhs m) ++ Z ∷ γ)
 push-all m w Z γ with fin0? (length (pushβ m)) in eqF0
 ... | nothing =
       subst (λ q → M′ ⊢ₚ (q , w , Z ∷ γ) ⟹* (Sim (tgt m) , w , map just (rhs m) ++ Z ∷ γ))
             (sym (popTargetV-ready m len≡0))
             (subst (λ rr → M′ ⊢ₚ (Sim (tgt m) , w , Z ∷ γ)
                                  ⟹* (Sim (tgt m) , w , map just rr ++ Z ∷ γ))
                    (sym rhsNil) ε)
   where len≡0 : length (pushβ m) ≡ 0
         len≡0 = fin0?-zero (length (pushβ m)) eqF0
         rhsNil : rhs m ≡ []
         rhsNil = len0 (rhs m) (trans (sym (length-reverse (rhs m))) len≡0)
 ... | just j =
       subst (λ q → M′ ⊢ₚ (q , w , Z ∷ γ) ⟹* (Sim (tgt m) , w , map just (rhs m) ++ Z ∷ γ))
             (sym (popTargetV-start m (proj₂ (fin0?-sucL (length (pushβ m)) eqF0))))
             (subst (λ s → M′ ⊢ₚ (Strt m , w , Z ∷ γ) ⟹* (Sim (tgt m) , w , s))
                    (cong (_++ Z ∷ γ) pushedβ-rhs)
                    (startPush-iter m j w Z γ eqF0 (<-wellFounded _)))
   where
     pushedβ-rhs : pushedβ m j ≡ map just (rhs m)
     pushedβ-rhs = trans (cong (λ k → map just (reverse (drop k (pushβ m))))
                               (fin0?-fzero (length (pushβ m)) eqF0))
                         (cong (map just) (reverse-involutive (rhs m)))

 push-all-enc : (m : Move) (w : List T) (s : List Γ)
              → M′ ⊢ₚ (popTarget m , w , enc s) ⟹* (Sim (tgt m) , w , map just (rhs m) ++ enc s)
 push-all-enc m w s with enc-cons s
 ... | Z , γ , eq =
       subst (λ zg → M′ ⊢ₚ (popTarget m , w , zg) ⟹* (Sim (tgt m) , w , map just (rhs m) ++ zg))
             (sym eq) (push-all m w Z γ)

 -- Stack equality for the macro: map just β ++ enc s ≡ enc (β ++ s).
 mapjust-enc : (β s : List Γ) → map just β ++ enc s ≡ enc (β ++ s)
 mapjust-enc β s = trans (sym (++-assoc (map just β) (map just s) (nothing ∷ [])))
                         (cong (_++ nothing ∷ []) (sym (map-++ just β s)))

 -- One move of M (read or ε) becomes one macro of M′.
 sim-move-read : {q : Q} {a : T} {A : Γ} {w′ : List T} {s′ : List Γ} {r : Q} {β : List Γ}
               → (r , β) ∈ M .δ q (just a) A
               → M′ ⊢ₚ (Sim q , a ∷ w′ , enc (A ∷ s′)) ⟹* (Sim r , w′ , enc (β ++ s′))
 sim-move-read {q} {a} {A} {w′} {s′} {r} {β} mem =
   subst (λ c → M′ ⊢ₚ (Sim q , a ∷ w′ , enc (A ∷ s′)) ⟹* c) finalEq
         (read mem′ ◅ push-all-enc m w′ s′)
   where
     m : Move
     m = (q , just a , A , index mem)
     lkeq : lookup (M .δ q (just a) A) (index mem) ≡ (r , β)
     lkeq = sym (lookup-index mem)
     mem′ : (popTarget m , []) ∈ popList q (just a) A
     mem′ = ∈-map⁺ _ (anyAllFins (index mem) refl)
     finalEq : (Sim (tgt m) , w′ , map just (rhs m) ++ enc s′) ≡ (Sim r , w′ , enc (β ++ s′))
     finalEq = cong₂ (λ st stk → st , w′ , stk) (cong Sim (cong proj₁ lkeq))
                     (trans (cong (λ rr → map just rr ++ enc s′) (cong proj₂ lkeq))
                            (mapjust-enc β s′))

 sim-move-eps : {q : Q} {A : Γ} {w′ : List T} {s′ : List Γ} {r : Q} {β : List Γ}
              → (r , β) ∈ M .δ q nothing A
              → M′ ⊢ₚ (Sim q , w′ , enc (A ∷ s′)) ⟹* (Sim r , w′ , enc (β ++ s′))
 sim-move-eps {q} {A} {w′} {s′} {r} {β} mem =
   subst (λ c → M′ ⊢ₚ (Sim q , w′ , enc (A ∷ s′)) ⟹* c) finalEq
         (eps mem′ ◅ push-all-enc m w′ s′)
   where
     m : Move
     m = (q , nothing , A , index mem)
     lkeq : lookup (M .δ q nothing A) (index mem) ≡ (r , β)
     lkeq = sym (lookup-index mem)
     mem′ : (popTarget m , []) ∈ popList q nothing A
     mem′ = ∈-map⁺ _ (anyAllFins (index mem) refl)
     finalEq : (Sim (tgt m) , w′ , map just (rhs m) ++ enc s′) ≡ (Sim r , w′ , enc (β ++ s′))
     finalEq = cong₂ (λ st stk → st , w′ , stk) (cong Sim (cong proj₁ lkeq))
                     (trans (cong (λ rr → map just rr ++ enc s′) (cong proj₂ lkeq))
                            (mapjust-enc β s′))

 -- Chains the run of M inside M′ (between the macros).
 run-sim : {q qf : Q} {w : List T} {s : List Γ}
         → M ⊢ₚ (q , w , s) ⟹* (qf , [] , [])
         → M′ ⊢ₚ (Sim q , w , enc s) ⟹* (Sim qf , [] , enc [])
 run-sim ε = ε
 run-sim (read mem ◅ rest) = ⟹*ₚ-trans (sim-move-read mem) (run-sim rest)
 run-sim (eps mem ◅ rest) = ⟹*ₚ-trans (sim-move-eps mem) (run-sim rest)

 normalize-complete : (w : List T) → AccES M w → AccES M′ w
 normalize-complete w (qf , d) =
   Sim qf , eps (here refl) ◅ ⟹*ₚ-trans (run-sim d) (eps (here refl) ◅ ε)

 -- ════════════════════════════════════════════════════════════════
 -- SOUNDNESS: AccES M′ w → AccES M w   (inverting the macros)
 -- ════════════════════════════════════════════════════════════════

 ∈-lookup : {A : Set} (xs : List A) (i : Fin (length xs)) → lookup xs i ∈ xs
 ∈-lookup (x ∷ xs) fzero = here refl
 ∈-lookup (x ∷ xs) (fsuc i) = there (∈-lookup xs i)

 popList-sound : (q : Q) (mt : Maybe T) (A : Γ)
               → ∀ {r β} → (r , β) ∈ popList q mt A
               → ∃ λ i → r ≡ popTarget (q , mt , A , i) × β ≡ []
 popList-sound q mt A mem with ∈-map⁻ _ mem
 ... | i , _ , refl = i , refl , refl

 pushMove-sound : (m : Move) (j : Fin (length (pushβ m))) (Z : Maybe Γ)
                → ∀ {r β} → (r , β) ∈ pushMove m j Z
                → β ≡ just (lookup (pushβ m) j) ∷ Z ∷ []
                  × ((∃ λ j′ → r ≡ Psh m j′ × finSucc? j ≡ just j′)
                     ⊎ (r ≡ Sim (tgt m) × finSucc? j ≡ nothing))
 pushMove-sound m j Z mem with finSucc? j
 pushMove-sound m j Z (here refl) | just j′ = refl , inj₁ (j′ , refl , refl)
 pushMove-sound m j Z (there ()) | just j′
 pushMove-sound m j Z (here refl) | nothing = refl , inj₂ (refl , refl)
 pushMove-sound m j Z (there ()) | nothing

 startPushMove-sound : (m : Move) (Z : Maybe Γ)
                     → ∀ {r β} → (r , β) ∈ startPushMove m Z
                     → ∃ λ j → fin0? (length (pushβ m)) ≡ just j
                       × β ≡ just (lookup (pushβ m) j) ∷ Z ∷ []
                       × ((∃ λ j′ → r ≡ Psh m j′ × finSucc? j ≡ just j′)
                          ⊎ (r ≡ Sim (tgt m) × finSucc? j ≡ nothing))
 startPushMove-sound m Z mem with fin0? (length (pushβ m))
 ... | just j = let (be , rr) = pushMove-sound m j Z mem in j , refl , be , rr
 startPushMove-sound m Z () | nothing

 -- ── pure lemmas about the pushed stack (they mirror npda-sound) ──

 reverse-take-suc : (m : Move) (j : Fin (length (pushβ m)))
   → reverse (take (suc (toℕ j)) (pushβ m))
     ≡ lookup (pushβ m) j ∷ reverse (take (toℕ j) (pushβ m))
 reverse-take-suc m j =
   trans (cong reverse (take-suc (pushβ m) j))
         (reverse-++ (take (toℕ j) (pushβ m)) (lookup (pushβ m) j ∷ []))

 decomp-step : (m : Move) (j j′ : Fin (length (pushβ m))) (σ : List (Maybe Γ)) (s′ : List Γ)
   → finSucc? j ≡ just j′
   → σ ≡ map just (reverse (take (toℕ j) (pushβ m))) ++ enc s′
   → just (lookup (pushβ m) j) ∷ σ ≡ map just (reverse (take (toℕ j′) (pushβ m))) ++ enc s′
 decomp-step m j j′ σ s′ fseq seq = begin
   just (lookup (pushβ m) j) ∷ σ
     ≡⟨ cong (just (lookup (pushβ m) j) ∷_) seq ⟩
   map just (lookup (pushβ m) j ∷ reverse (take (toℕ j) (pushβ m))) ++ enc s′
     ≡⟨ cong (λ l → map just l ++ enc s′) (sym (reverse-take-suc m j)) ⟩
   map just (reverse (take (suc (toℕ j)) (pushβ m))) ++ enc s′
     ≡⟨ cong (λ k → map just (reverse (take k (pushβ m))) ++ enc s′)
             (sym (finSucc?-just j j′ fseq)) ⟩
   map just (reverse (take (toℕ j′) (pushβ m))) ++ enc s′ ∎

 collapse-eq : (m : Move) (j : Fin (length (pushβ m))) (σ : List (Maybe Γ)) (s′ : List Γ)
   → finSucc? j ≡ nothing
   → σ ≡ map just (reverse (take (toℕ j) (pushβ m))) ++ enc s′
   → just (lookup (pushβ m) j) ∷ σ ≡ enc (rhs m ++ s′)
 collapse-eq m j σ s′ fn seq = begin
   just (lookup (pushβ m) j) ∷ σ
     ≡⟨ cong (just (lookup (pushβ m) j) ∷_) seq ⟩
   map just (lookup (pushβ m) j ∷ reverse (take (toℕ j) (pushβ m))) ++ enc s′
     ≡⟨ cong (λ l → map just l ++ enc s′) (sym (reverse-take-suc m j)) ⟩
   map just (reverse (take (suc (toℕ j)) (pushβ m))) ++ enc s′
     ≡⟨ cong (λ k → map just (reverse (take k (pushβ m))) ++ enc s′)
             (finSucc?-last j fn) ⟩
   map just (reverse (take (length (pushβ m)) (pushβ m))) ++ enc s′
     ≡⟨ lastEq ⟩
   enc (rhs m ++ s′) ∎
   where
     lastEq : map just (reverse (take (length (pushβ m)) (pushβ m))) ++ enc s′ ≡ enc (rhs m ++ s′)
     lastEq = begin
       map just (reverse (take (length (pushβ m)) (pushβ m))) ++ enc s′
         ≡⟨ cong (λ l → map just (reverse l) ++ enc s′)
                 (take-all (length (pushβ m)) (pushβ m) ≤-refl) ⟩
       map just (reverse (reverse (rhs m))) ++ enc s′
         ≡⟨ cong (λ l → map just l ++ enc s′) (reverse-involutive (rhs m)) ⟩
       map just (rhs m) ++ enc s′
         ≡⟨ mapjust-enc (rhs m) s′ ⟩
       enc (rhs m ++ s′) ∎

 -- Empty stack ⇒ no step is possible ⇒ the run is ε (and the input is exhausted).
 from-empty : {st qa : State} {w : List T}
            → M′ ⊢ₚ (st , w , []) ⟹* (qa , [] , []) → w ≡ []
 from-empty ε = refl
 from-empty (() ◅ _)

 -- Stack invariant at Strt (j = fzero ⇒ toℕ j = 0 ⇒ empty prefix).
 strt-seq : (m : Move) (Z : Maybe Γ) (γ : List (Maybe Γ)) (s′ : List Γ)
            (j : Fin (length (pushβ m)))
          → Z ∷ γ ≡ enc s′ → fin0? (length (pushβ m)) ≡ just j
          → Z ∷ γ ≡ map just (reverse (take (toℕ j) (pushβ m))) ++ enc s′
 strt-seq m Z γ s′ j eqc eqf0 =
   trans eqc (sym (cong (λ k → map just (reverse (take k (pushβ m))) ++ enc s′)
                        (fin0?-fzero (length (pushβ m)) eqf0)))

 -- ── the inversion (mutual, structural on the run of M′) ──
 mutual
   -- Sim q, stack enc s: rebuilds the run of M from (q,w,s).
   inv-sim : (q : Q) (w : List T) (s : List Γ) {qa : State}
           → M′ ⊢ₚ (Sim q , w , enc s) ⟹* (qa , [] , [])
           → ∃ λ qf → M ⊢ₚ (q , w , s) ⟹* (qf , [] , [])
   inv-sim q w [] (read () ◅ _)
   inv-sim q w [] (eps (here refl) ◅ rest) with from-empty rest
   ... | refl = q , ε
   inv-sim q w [] (eps (there ()) ◅ _)
   inv-sim q (a ∷ w′) (A ∷ s′) (read mem ◅ rest) with popList-sound q (just a) A mem
   ... | i , refl , refl =
         let (qf , cont) = inv-dispatch (q , just a , A , i)
                             (length (pushβ (q , just a , A , i))) w′ s′ refl rest
         in qf , read (∈-lookup (M .δ q (just a) A) i) ◅ cont
   inv-sim q w (A ∷ s′) (eps mem ◅ rest) with popList-sound q nothing A mem
   ... | i , refl , refl =
         let (qf , cont) = inv-dispatch (q , nothing , A , i)
                             (length (pushβ (q , nothing , A , i))) w s′ refl rest
         in qf , eps (∈-lookup (M .δ q nothing A) i) ◅ cont

   -- Despacha o pós-pop conforme nº de símbolos a empilhar (length pushβ).
   inv-dispatch : (m : Move) (k : ℕ) (w : List T) (s′ : List Γ) {qa : State}
                → length (pushβ m) ≡ k
                → M′ ⊢ₚ (popTargetV m k , w , enc s′) ⟹* (qa , [] , [])
                → ∃ λ qf → M ⊢ₚ (tgt m , w , rhs m ++ s′) ⟹* (qf , [] , [])
   inv-dispatch m (suc n) w [] lenEq run = inv-start m w nothing [] [] refl run
   inv-dispatch m (suc n) w (x ∷ s″) lenEq run = inv-start m w (just x) (enc s″) (x ∷ s″) refl run
   inv-dispatch m zero w s′ lenEq run =
         let (qf , cont) = inv-sim (tgt m) w s′ run
         in qf , subst (λ ss → M ⊢ₚ (tgt m , w , ss) ⟹* (qf , [] , [])) (sym rhs++) cont
     where rhsNil : rhs m ≡ []
           rhsNil = len0 (rhs m) (trans (sym (length-reverse (rhs m))) lenEq)
           rhs++ : rhs m ++ s′ ≡ s′
           rhs++ = cong (_++ s′) rhsNil

   -- Strt m with stack Z∷γ (= enc s′): performs the first push.
   inv-start : (m : Move) (w : List T) (Z : Maybe Γ) (γ : List (Maybe Γ)) (s′ : List Γ)
               {qa : State}
             → Z ∷ γ ≡ enc s′
             → M′ ⊢ₚ (Strt m , w , Z ∷ γ) ⟹* (qa , [] , [])
             → ∃ λ qf → M ⊢ₚ (tgt m , w , rhs m ++ s′) ⟹* (qf , [] , [])
   inv-start m w Z γ s′ eqc (read () ◅ _)
   inv-start m w Z γ s′ eqc (eps mem ◅ rest) with startPushMove-sound m Z mem
   ... | j , eqf0 , refl , inj₁ (j′ , refl , fseq) =
         inv-push m j′ w (just (lookup (pushβ m) j)) (Z ∷ γ) s′
                  (decomp-step m j j′ (Z ∷ γ) s′ fseq (strt-seq m Z γ s′ j eqc eqf0)) rest
   inv-start m w Z γ s′ eqc (eps mem ◅ rest) | j , eqf0 , refl , inj₂ (refl , fn)
     rewrite collapse-eq m j (Z ∷ γ) s′ fn (strt-seq m Z γ s′ j eqc eqf0) =
         inv-sim (tgt m) w (rhs m ++ s′) rest

   -- Psh m j, stack top∷stk = (already pushed)++enc s′: keeps pushing.
   inv-push : (m : Move) (j : Fin (length (pushβ m))) (w : List T)
              (top : Maybe Γ) (stk : List (Maybe Γ)) (s′ : List Γ) {qa : State}
            → top ∷ stk ≡ map just (reverse (take (toℕ j) (pushβ m))) ++ enc s′
            → M′ ⊢ₚ (Psh m j , w , top ∷ stk) ⟹* (qa , [] , [])
            → ∃ λ qf → M ⊢ₚ (tgt m , w , rhs m ++ s′) ⟹* (qf , [] , [])
   inv-push m j w top stk s′ deq (read () ◅ _)
   inv-push m j w top stk s′ deq (eps mem ◅ rest) with pushMove-sound m j top mem
   ... | refl , inj₁ (j′ , refl , fseq) =
         inv-push m j′ w (just (lookup (pushβ m) j)) (top ∷ stk) s′
                  (decomp-step m j j′ (top ∷ stk) s′ fseq deq) rest
   inv-push m j w top stk s′ deq (eps mem ◅ rest) | refl , inj₂ (refl , fn)
     rewrite collapse-eq m j (top ∷ stk) s′ fn deq =
         inv-sim (tgt m) w (rhs m ++ s′) rest

 normalize-sound : (w : List T) → AccES M′ w → AccES M w
 normalize-sound w (q′ , read () ◅ _)
 normalize-sound w (q′ , eps (here refl) ◅ rest) = inv-sim (M .q₀) w (M .z₀ ∷ []) rest
 normalize-sound w (q′ , eps (there ()) ◅ _)

 -- ════════════════════════════════════════════════════════════════
 -- THEOREM: every PDA has a normal (±1) PDA with the VERY SAME language.
 --   hypothesis = an arbitrary PDA;  conclusion = an equivalent normal PDA.
 --   The equivalence holds for the FULL language (ε included).
 -- ════════════════════════════════════════════════════════════════
 normalize : ∃ λ (State′ : Set) → ∃ λ (M″ : PDA State′ T (Maybe Γ))
   → IsNormalPDA M″
   × Finite State′
   × (∀ w → AccES M″ w → AccES M w)
   × (∀ w → AccES M w → AccES M″ w)
 normalize = State , M′ , M′-normal , finite-State , normalize-sound , normalize-complete
