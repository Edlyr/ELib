{-# OPTIONS --cubical #-}

module ELib.Torsor.Trivialization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩ ; AbGroup→Group to GRP)
open import Cubical.Data.Sigma

open import ELib.Torsor.Base
open import ELib.Gerbe.Base
open import ELib.Gerbe.S
open import ELib.Gerbe.Link
open import ELib.Gerbe.B2

private
  variable
    ℓ ℓ' : Level

module _ (A : AbGroup {ℓ}) (G : B² A {ℓ}) where
  TA : Torsor (GRP A)
  TA = principalTorsor (GRP A)

  PG : Gerbe {ℓ-suc ℓ}
  PG = gerbe (Torsor (GRP A)) (isgerbe ∣ PT _ ∣ isGroupoidTorsor conn comm) where
    abstract
      pre-conn : (T : Torsor (GRP A)) → ∥ PT _ ≡ T ∥
      pre-conn T = recPropTrunc propTruncIsProp (λ t₀ → ∣ uaTorsor (trivialize T t₀) ∣) (Torsor.inhabited T)

      conn : (T T' : Torsor (GRP A)) → ∥ T ≡ T' ∥
      conn T T' = recPropTrunc propTruncIsProp (λ pT → recPropTrunc propTruncIsProp (λ pT' → ∣ sym pT ∙ pT' ∣) (pre-conn T')) (pre-conn T)

      pre-comm : (x y : PT _ ≡ PT _) → x ∙ y ≡ y ∙ x
      pre-comm x y = f-inj (x ∙ y) (y ∙ x) (isHom x y ∙ comm (f x) (f y) ∙ sym (isHom y x)) where
        open AbGroup A
        equiv : GroupEquiv (ΩB (GRP A)) (GRP A)
        equiv = compGroupEquiv (groupequiv (idEquiv _) λ _ _ → refl) (finalLemma (GRP A))
        open GroupEquiv equiv
        f = fst eq
        f-inj : (a b : _) → f a ≡ f b → a ≡ b
        f-inj a b p = a ≡⟨ sym (secEq eq a) ⟩ invEq eq (f a) ≡⟨ cong (invEq eq) p ⟩ invEq eq (f b) ≡⟨ secEq eq b ⟩ b ∎

      comm : (x : _) → (p q : x ≡ x) → p ∙ q ≡ q ∙ p
      comm x = recPropTrunc (isPropΠ2 λ _ _ → isGroupoidTorsor _ _ _ _) (λ path →
        transport (cong (λ r → (p q : r ≡ r) → p ∙ q ≡ q ∙ p) path) pre-comm) (pre-conn x)

  principalLink : Link PG A
  principalLink = makeLink-pnt (groupequiv eq isHom)
    where open GroupEquiv (finalLemma (GRP A))
    -- here we can't use finalLemma directly, since even though (π PG PT) has
    -- the same Carrier and law as ΩB, they are not judgmentally equal.

  torsors : B² A
  torsors = b² PG principalLink

  module PG = B² torsors

  ----------
  module G = B² G
  torsor-G : G.Carrier → G.Carrier → Torsor (GRP A)
  torsor-G x y = torsor X _⋆_ is-torsor where
    X : Type _
    X = x ≡ y
    _⋆_ : X → Ab⟨ A ⟩ → X
    p ⋆ g = p ∙ invEq (G.eq y) g
    postulate
      is-torsor : IsTorsor (GRP A) X _⋆_
    {-is-torsor = istorsor (G.grpd x y) (G.conn x y)
      (λ p g g' →
         (p ∙ invEq (G.eq y) g) ∙ invEq (G.eq y) g' ≡⟨ sym (assoc _ _ _) ⟩
         p ∙ invEq (G.eq y) g ∙ invEq (G.eq y) g' ≡⟨ cong (p ∙_) (sym (isGroupHomInv (G.group-equiv y) g g')) ⟩
         p ∙ invEq (G.eq y) (g A.+ g') ∎)
      {!!} {!!} {!!} {!!}-}

  module _ (x₀ : G.Carrier) where
    triv : G.Carrier → PG.Carrier
    triv = torsor-G x₀

    isEquivTriv : isEquiv triv
    equiv-proof isEquivTriv T = recPropTrunc isPropIsContr (λ p → subst (isContr ∘ fiber triv) p contrTA) (PG.conn TA T) where
      equiv : fiber triv TA ≃ (Σ[ x ∈ G.Carrier ] x₀ ≡ x)
      equiv =
        fiber triv TA                               ≃⟨ idEquiv _ ⟩
        Σ G.Carrier (λ x → triv x ≡ TA)             ≃⟨ Σ-cong-equiv-snd (λ x → compEquiv (invEquiv (TorsorPath _ _)) (torsorEquivSwap _ _)) ⟩
        Σ G.Carrier (λ x → TorsorEquiv TA (triv x)) ≃⟨ Σ-cong-equiv-snd (λ x → invEquiv (trivializeEquiv (triv x))) ⟩
        Σ G.Carrier (λ x → x₀ ≡ x) ■

      contrTA : isContr (fiber triv TA)
      contrTA = isOfHLevelRespectEquiv 0 (invEquiv equiv) lemma where
        lemma : isContr (Σ[ x ∈ G.Carrier ] x₀ ≡ x)
        lemma = ((x₀ , refl) , λ (x , p) → λ i → p i , λ j → p (i ∧ j))

  trivializeGerbe : G.Carrier → B²Equiv A G torsors --G.Carrier ≃ PG.Carrier
  trivializeGerbe x₀ = b²equiv (triv x₀) lemma where --triv x₀ , isEquivTriv x₀
    open AbGroup A hiding (assoc)
    module T₀ = Torsor (triv x₀ x₀)
    T₀ = triv x₀ x₀
    lemma : congLink G.lnk PG.lnk (triv x₀) ≡ grouphom (λ x → x) (λ _ _ → refl)
    lemma = congLink-carac _ _ _ x₀ ∙ groupHomEq (
      PG.e T₀ ∘ cong (triv x₀) ∘ invEq (G.eq x₀)
        ≡⟨ cong (_∘ cong (triv x₀) ∘ invEq (G.eq x₀)) (PG.coherence T₀ TA) ⟩
      PG.e TA ∘ PG.s T₀ TA ∘ cong (triv x₀) ∘ invEq (G.eq x₀)
        ≡⟨ cong (λ f → PG.e TA ∘ f ∘ cong (triv x₀) ∘ invEq (G.eq x₀)) (funExt (PG.s-carac _ _ p)) ⟩
      PG.e TA ∘ (λ q → sym p ∙ q ∙ p) ∘ cong (triv x₀) ∘ invEq (G.eq x₀)
        ≡⟨ cong (λ f → PG.e TA ∘ (λ q → sym p ∙ q ∙ p) ∘ f ∘ invEq (G.eq x₀))  (funExt (subLemma1 x₀)) ⟩
      PG.e TA ∘ (λ q → sym p ∙ (p ∙ p' q) ∙ p) ∘ invEq (G.eq x₀)
        ≡⟨ cong (λ f → PG.e TA ∘ f ∘ invEq (G.eq x₀)) (funExt λ q → (assoc (sym p) (p ∙ p' q) p) ∙ cong (_∙ p) (compPathl-cancel (sym p) (p' q))) ⟩
      PG.e TA ∘ (λ q → p' q ∙ p) ∘ invEq (G.eq x₀)
        ≡⟨ cong (_∘ (λ q → p' q ∙ p) ∘ invEq (G.eq x₀)) (funExt subLemma0) ⟩
      (λ a → - transport (cong Torsor.Carrier (p' (invEq (G.eq x₀) a) ∙ p)) 0g)
        ≡⟨ (funExt λ a → cong -_ (subLemma3 a)) ⟩
      (λ a → - a)
        ≡⟨ {!!} ⟩
      (λ a → a) ∎) where
      open GroupEquiv (finalLemma (GRP A))
      p : T₀ ≡ TA
      p = sym (uaTorsor (trivialize T₀ refl))
      p' : x₀ ≡ x₀ → TA ≡ T₀
      p' q = uaTorsor (trivialize T₀ q)
      subLemma0 : (q : TA ≡ TA) → PG.e TA q ≡ - transport (cong Torsor.Carrier q) 0g
      subLemma0 q =
        (eq .fst ∘ PG.s TA TA) q
          ≡⟨ cong (λ f → (eq .fst ∘ f) q) (B².s-id torsors TA) ⟩
        - transport (cong Torsor.Carrier q) 0g ∎

      subLemma1 : (x : G.Carrier) (q : x₀ ≡ x) → cong {x = x₀} {y = x} (triv x₀) q ≡ p ∙ uaTorsor (trivialize (triv x₀ x) q)
      subLemma1 x = J (λ x q → cong {x = x₀} {y = x} (triv x₀) q ≡ p ∙ uaTorsor (trivialize (triv x₀ x) q))
        (torsorPathEq _ _ (cong (cong Torsor.Carrier) subLemma)) where
        subLemma : refl ≡ p ∙ uaTorsor (trivialize T₀ refl)
        subLemma = sym (lCancel _)
        
      preSubLemma2 : (q : x₀ ≡ x₀) → cong Torsor.Carrier (p' q ∙ p) ≡
        ua (compEquiv (TorsorEquiv.eq (trivialize T₀ q)) (invEquiv (TorsorEquiv.eq (trivialize T₀ refl))))
      preSubLemma2 q =
        cong Torsor.Carrier (p' q ∙ p)
          ≡⟨ cong-∙ Torsor.Carrier (p' q) p ⟩
        cong Torsor.Carrier (p' q) ∙ cong Torsor.Carrier p
          ≡⟨ (λ i → carac-uaTorsor (trivialize T₀ q) i ∙ cong sym (carac-uaTorsor (trivialize T₀ refl)) i) ⟩
        ua (TorsorEquiv.eq (trivialize T₀ q)) ∙ sym (ua (TorsorEquiv.eq (trivialize T₀ refl)))
          ≡⟨ cong (ua (TorsorEquiv.eq (trivialize T₀ q)) ∙_) (sym (uaInvEquiv (TorsorEquiv.eq (trivialize T₀ refl)))) ⟩
        ua (TorsorEquiv.eq (trivialize T₀ q)) ∙ ua (invEquiv (TorsorEquiv.eq (trivialize T₀ refl)))
          ≡⟨ sym (uaCompEquiv _ _) ⟩
        ua (compEquiv (TorsorEquiv.eq (trivialize T₀ q)) (invEquiv (TorsorEquiv.eq (trivialize T₀ refl)))) ∎

      subLemma2 : (q : x₀ ≡ x₀) → transport (cong Torsor.Carrier (p' q ∙ p)) ≡ (λ a → G.e x₀ q + a)
      subLemma2 q =
        transport (cong Torsor.Carrier (p' q ∙ p))
          ≡⟨ cong transport (preSubLemma2 q) ⟩
        transport (ua (compEquiv (TorsorEquiv.eq (trivialize T₀ q)) (invEquiv (TorsorEquiv.eq (trivialize T₀ refl)))))
          ≡⟨ funExt (uaβ (compEquiv (TorsorEquiv.eq (trivialize T₀ q)) (invEquiv (TorsorEquiv.eq (trivialize T₀ refl))))) ⟩
        (λ a → T₀.trans refl (q T₀.⋆ a))
          ≡⟨ funExt (λ a → T₀.trans-unique refl (q ∙ invEq (G.eq x₀) a) (G.e x₀ q + a) (helper a)) ⟩
        (λ a → G.e x₀ q + a) ∎ where
          helper : (a : _) → refl T₀.⋆ (G.e x₀ q + a) ≡ q ∙ invEq (G.eq x₀) a
          helper a =
            refl ∙ invEq (G.eq x₀) (G.e x₀ q + a)          ≡⟨ sym (lUnit _) ⟩
            invEq (G.eq x₀) (G.e x₀ q + a)                 ≡⟨ isGroupHomInv (G.group-equiv x₀) (G.e x₀ q) a ⟩
            invEq (G.eq x₀) (G.e x₀ q) ∙ invEq (G.eq x₀) a ≡⟨ cong (_∙ _) (secEq (G.eq x₀) q) ⟩
            q ∙ invEq (G.eq x₀) a ∎

      subLemma3 : (a : Ab⟨ A ⟩) → transport (cong Torsor.Carrier (p' (invEq (G.eq x₀) a) ∙ p)) 0g ≡ a
      subLemma3 a =
        transport (cong Torsor.Carrier (p' (invEq (G.eq x₀) a) ∙ p)) 0g ≡⟨ (λ i → subLemma2 (invEq (G.eq x₀) a) i 0g) ⟩
        (G.e x₀ (invEq (G.eq x₀) a) + 0g) ≡⟨ cong (_+ 0g) (retEq (G.eq x₀) a) ⟩
        a + 0g ≡⟨ rid a ⟩
        a ∎
{-
  deTrivialize : G.Carrier ≃ PG.Carrier → G.Carrier
  deTrivialize eq = invEq eq TA

  retr : retract trivializeGerbe deTrivialize
  retr x₀ = transportRefl x₀

  sec : section trivializeGerbe deTrivialize
  sec eq = equivEq _ _ lemma where
    x₀ : G.Carrier
    x₀ = deTrivialize eq
    p₀ : TA ≡ triv x₀ x₀
    p₀ = uaTorsor (trivialize (triv x₀ x₀) refl)
    p : fst eq x₀ ≡ triv x₀ x₀
    p = retEq eq TA ∙ p₀

    pre-lemma0 : (x : G.Carrier) (q : x₀ ≡ x) → cong {x = x₀} {y = x} (triv x₀) q ≡ sym p₀ ∙ uaTorsor (trivialize (triv x₀ x) q)
    pre-lemma0 x = J (λ x q → cong {x = x₀} {y = x} (triv x₀) q ≡ sym p₀ ∙ uaTorsor (trivialize (triv x₀ x) q))
      (torsorPathEq _ _ (cong (cong Torsor.Carrier) subLemma)) where
      subLemma : refl ≡ sym p₀ ∙ uaTorsor (trivialize (triv x₀ x₀) refl)
      subLemma = sym (lCancel _)

    lemma0 : (q : x₀ ≡ x₀) → p ∙ cong (triv x₀) q ≡ cong (fst eq) q ∙ p
    lemma0 q =
      p ∙ cong (triv x₀) q                               ≡⟨ cong (p ∙_) (pre-lemma0 x₀ q) ⟩
      p ∙ sym p₀ ∙ uaTorsor (trivialize (triv x₀ x₀) q)  ≡⟨ sym (assoc _ _ _) ∙ cong (retEq eq TA ∙_) (compPathl-cancel p₀ _) ⟩
      retEq eq TA ∙ uaTorsor (trivialize (triv x₀ x₀) q) ≡⟨ torsorPathEq _ _ subLemma ⟩
      cong (fst eq) q ∙ p ∎
      where
      subLemma : cong Torsor.Carrier (retEq eq TA ∙ uaTorsor (trivialize (triv x₀ x₀) q)) ≡ cong Torsor.Carrier (cong (fst eq) q ∙ p)
      subLemma =
        cong Torsor.Carrier (retEq eq TA ∙ uaTorsor (trivialize (triv x₀ x₀) q))
          ≡⟨ cong-∙ Torsor.Carrier (retEq eq TA) (uaTorsor (trivialize (triv x₀ x₀) q)) ⟩
        cong Torsor.Carrier (retEq eq TA) ∙ cong Torsor.Carrier (uaTorsor (trivialize (triv x₀ x₀) q))
          ≡⟨ cong (cong Torsor.Carrier (retEq eq TA) ∙_) (carac-uaTorsor _) ⟩
        cong Torsor.Carrier (retEq eq TA) ∙ ua (TorsorEquiv.eq (trivialize (triv x₀ x₀) q))
          ≡⟨ {!TorsorEquiv.eq (trivialize (triv x₀ x₀) q)!} ⟩
        cong Torsor.Carrier (cong (fst eq) q ∙ p) ∎

    lemma : triv x₀ ≡ fst eq
    lemma = {!!}
  
-}
