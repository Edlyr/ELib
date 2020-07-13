{-# OPTIONS --cubical #-}

module ELib.Torsor.Trivialization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩ ; AbGroup→Group to GRP)
open import Cubical.Data.Sigma

open import ELib.Torsor.Base
open import ELib.Gerbe.Base
open import ELib.Gerbe.Link
open import ELib.Gerbe.B2

private
  variable
    ℓ ℓ' : Level

module _ (A : AbGroup {ℓ}) (G : B² A {ℓ}) (x₀ : B².Carrier G) where
  TA : Torsor (GRP A)
  TA = principalTorsor (GRP A)

  PG : Gerbe {ℓ-suc ℓ}
  PG = gerbe (Torsor (GRP A)) (isgerbe ∣ PT _ ∣ isGroupoidTorsor conn comm) where
    pre-conn : (T : Torsor (GRP A)) → ∥ PT _ ≡ T ∥
    pre-conn T = recPropTrunc propTruncIsProp (λ t₀ → ∣ uaTorsor (trivialize T t₀) ∣) (Torsor.inhabited T)

    conn : (T T' : Torsor (GRP A)) → ∥ T ≡ T' ∥
    conn T T' = recPropTrunc propTruncIsProp (λ pT → recPropTrunc propTruncIsProp (λ pT' → ∣ sym pT ∙ pT' ∣) (pre-conn T')) (pre-conn T)

    pre-comm : (x y : PT _ ≡ PT _) → x ∙ y ≡ y ∙ x
    pre-comm x y = f-inj (x ∙ y) (y ∙ x) (isHom _ _ ∙ comm _ _ ∙ sym (isHom _ _)) where
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
