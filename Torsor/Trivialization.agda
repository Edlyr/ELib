{-# OPTIONS --cubical #-}

module ELib.Torsor.Trivialization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
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
  test1 : G.Carrier → PG.Carrier
  test1 = torsor-G x₀

  test2 : isEquiv test1
  equiv-proof test2 y = {!!} where
    pnt₀ : fiber test1 (test1 x₀)
    pnt₀ = x₀ , refl --uaTorsor (invTorsorEquiv (trivialize (test1 x₀) refl))

    test0 : fiber test1 TA ≃ (Σ[ x ∈ G.Carrier ] x₀ ≡ x)
    test0 =
      fiber test1 TA                               ≃⟨ idEquiv _ ⟩
      Σ G.Carrier (λ x → test1 x ≡ TA)             ≃⟨ Σ-cong-equiv-snd (λ x → compEquiv (invEquiv (TorsorPath _ _)) (torsorEquivSwap _ _)) ⟩
      Σ G.Carrier (λ x → TorsorEquiv TA (test1 x)) ≃⟨ Σ-cong-equiv-snd (λ x → invEquiv (trivializeEquiv (test1 x))) ⟩
      Σ G.Carrier (λ x → x₀ ≡ x) ■

    {-prop : (α : fiber test1 (test1 x₀)) → pnt₀ ≡ α
    prop (x , p) = ΣPathP (subst Torsor.Carrier (sym p) refl , {!!}) where
      lemma : cong test1 (subst Torsor.Carrier (sym p) refl) ≡ sym p
      lemma = torsorPathEq _ _ (
        cong Torsor.Carrier (cong test1 (subst Torsor.Carrier (sym p) refl))
          ≡⟨ {!!} ⟩
        cong Torsor.Carrier (sym p) ∎)
      test : I → {!!}
      test i = {!Torsor.Carrier
       (test1 (subst Torsor.Carrier (λ i₁ → p (~ i₁)) (λ _ → x₀) i))!}-}


{- Trying to see under which assumptions the following might hold
TheBigLemma : {A : Type ℓ} (x y : A) (p : (x ≡ x) ≡ (x ≡ y)) (q : x ≡ x) → transport p q ≡ transport (λ i → x ≡ transport p refl i) q
TheBigLemma {A = A} x y p q = {!!} where
  lemma : (z : A) (q : x ≡ z) (p : (x ≡ z) ≡ (x ≡ y)) → transport p q ≡ transport (λ i → x ≡ (sym q ∙ transport p q) i) q
  lemma z = J (λ z q → (p : (x ≡ z) ≡ (x ≡ y)) → transport p q ≡ transport (λ i → x ≡ (sym q ∙ transport p q) i) q)
    λ p → sym (fromPathP {A = λ i → x ≡ (refl ∙ transport p refl) i} (transport (sym (PathP≡compPath _ _ _)) (sym (lUnit _ ∙ lUnit _))))
-}
