{-# OPTIONS --cubical #-}

module ELib.B1.MorphismDelooping where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import ELib.UsefulLemmas
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

private
  variable
    ℓ ℓ' : Level

module Delooping {A : Type ℓ} {B : Type ℓ'} (isConnA : (x y : A) → ∥ x ≡ y ∥) (isGrpdB : isGroupoid B) {a : A} {b : B}
  (f : a ≡ a → b ≡ b) (isHom-f : (x y : a ≡ a) → f (x ∙ y) ≡ f x ∙ f y) where
  C : A → Type _
  C x = Σ[ y ∈ B ] Σ[ p ∈ (a ≡ x → b ≡ y) ] ((ω : a ≡ a) (α : a ≡ x) → p (ω ∙ α) ≡ f ω ∙ p α)

  propCa : isProp (C a)
  propCa (y , p , !) (y' , p' , !') = ΣPathP (sym (p refl) ∙ p' refl , toPathP (Σ≡Prop (λ _ → isPropΠ2 λ _ _ → isGrpdB _ _ _ _)
    (funExt λ ok →
      fromPathP {A = (λ i → b ≡ (sym (p refl) ∙ p' refl) i)} {x = p (transport refl ok)} {y = p' ok}
        (transport (sym (PathP≡compPath _ _ _)) (
        p (transport refl ok) ∙ sym (p refl) ∙ p' refl
          ≡⟨ cong (λ x → p x ∙ sym (p refl) ∙ p' refl) (transportRefl ok ∙ rUnit ok) ⟩
        p (ok ∙ refl) ∙ sym (p refl) ∙ p' refl
          ≡⟨ cong (λ x → x ∙ sym (p refl) ∙ p' refl) (! ok refl) ∙ sym (assoc _ _ _) ⟩
        f ok ∙ p refl ∙ sym (p refl) ∙ p' refl
          ≡⟨ cong (f ok ∙_) (assoc _ _ _ ∙ cong (_∙ p' refl) (rCancel (p refl)) ∙ sym (lUnit (p' refl))) ⟩
        f ok ∙ p' refl
          ≡⟨ sym (cong p' (rUnit ok) ∙ !' ok refl) ⟩
        p' ok ∎
      )))))

  propC : (x : A) → isProp (C x)
  propC x = recPropTrunc isPropIsProp (λ p → transport (λ i → isProp (C (p i))) propCa) (isConnA a x)

  carac-propCa : propC a ≡ propCa
  carac-propCa = isPropIsProp _ _
    
  contrCa : isContr (C a)
  contrCa = (b , f , isHom-f) , propCa _

  contrC : (x : A) → isContr (C x)
  contrC x = recPropTrunc isPropIsContr (λ p → transport (λ i → isContr (C (p i))) contrCa) (isConnA a x)

---------------

  isDeloop : (A → B) → Type _
  isDeloop g = Σ[ p ∈ (b ≡ g a) ] ((q : a ≡ a) → p ∙ cong g q ≡ f q ∙ p)
  deloopingType : Type _
  deloopingType = Σ[ g ∈ (A → B) ] (isDeloop g)

  deloop : deloopingType
  deloop = g , pr , carac-cong where
    g : A → B
    g x = fst (fst (contrC x))

    p : (x : A) → a ≡ x → b ≡ g x
    p x q = contrC x .fst .snd .fst q
    pr = p a refl

    ! : (x : A) (ω : a ≡ a) (α : a ≡ x) → p x (ω ∙ α) ≡ f ω ∙ p x α
    ! x = contrC x .fst .snd .snd

    lemma : (x : A) (α : a ≡ x) (x' : A) (q : x ≡ x') → p x α ∙ cong g q ≡ p x' (α ∙ q)
    lemma x α x' = J (λ x' q → p x α ∙ cong g q ≡ p x' (α ∙ q))
      (sym (rUnit _) ∙ cong (p x) (rUnit _))

    carac-cong : (q : a ≡ a) → pr ∙ cong g q ≡ f q ∙ pr
    carac-cong q = lemma a refl a q ∙ cong (p a) (sym (lUnit _) ∙ rUnit _) ∙ ! a q refl

-----------------

  C-fun : deloopingType → (x : A) → C x
  C-fun (g , p , !) x = g x , (λ q → p ∙ cong g q) , λ ω α →
    p ∙ cong g (ω ∙ α)
      ≡⟨ cong (p ∙_) (cong-∙ g ω α) ∙ assoc _ _ _ ⟩
    (p ∙ cong g ω) ∙ cong g α
      ≡⟨ cong (_∙ cong g α) (! ω) ∙ sym (assoc _ _ _) ⟩
    f ω ∙ p ∙ cong g α ∎

  propDeloop : isProp deloopingType
  propDeloop (g , p , !) (g' , p' , !') = ΣPathP (g≡g' , toPathP (Σ≡Prop (λ _ → isPropΠ λ _ → isGrpdB _ _ _ _)
    (fromPathP {A = λ i → b ≡ g≡g' i a} {x = p} {y = p'} (transport (sym (PathP≡compPath _ _ _))
      (p ∙ path
        ≡⟨ cong (p ∙_ ) path≡path' ⟩
      p ∙ sym (p ∙ refl) ∙ p' ∙ refl
        ≡⟨ assoc _ _ _ ∙ cong (_∙ p' ∙ refl) (cong (p ∙_) (sym (rUnit _)) ∙ rCancel p) ⟩
      refl ∙ p' ∙ refl
        ≡⟨ sym (rUnit _ ∙ lUnit _) ⟩
      p' ∎)
      )))) where
    Cg = C-fun (g , p , !)
    Cg' = C-fun (g' , p' , !')

    g≡g' : g ≡ g'
    g≡g' = funExt λ x → cong fst (propC x (Cg x) (Cg' x))

    path : g a ≡ g' a
    path = λ i → g≡g' i a

    path' : g a ≡ g' a
    path' = cong fst (propCa (Cg a) (Cg' a)) -- = sym (p ∙ refl) ∙ p' ∙ refl

    path≡path' : path ≡ path'
    path≡path' = λ i → cong fst (carac-propCa i (Cg a) (Cg' a))
