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
  carac-propCa = 
    recPropTrunc isPropIsProp (λ p → transport (λ i → isProp (C (p i))) propCa) (isConnA a a)
      ≡⟨ (λ j → recPropTrunc isPropIsProp (λ p → transport (λ i → isProp (C (p i))) propCa) (propTruncIsProp (isConnA a a) ∣ refl ∣ j)) ⟩
    recPropTrunc isPropIsProp (λ p → transport (λ i → isProp (C (p i))) propCa) (∣ refl ∣)
      ≡⟨ transportRefl propCa ⟩
    propCa ∎
    

  contrCa : isContr (C a)
  contrCa = (b , f , isHom-f) , propCa _

  contrC : (x : A) → isContr (C x)
  contrC x = recPropTrunc isPropIsContr (λ p → transport (λ i → isContr (C (p i))) contrCa) (isConnA a x)

  deloopingType : Type _
  deloopingType = Σ[ g ∈ (A → B) ] Σ[ p ∈ (b ≡ g a) ] ((q : a ≡ a) → p ∙ cong g q ≡ f q ∙ p)

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
      
  


abstract
  deloopMorphism : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} → ((x y : A) → ∥ x ≡ y ∥) → (isGroupoid B) → {a : A} {b : B}
    (f : a ≡ a → b ≡ b) → ((x y : a ≡ a) → f (x ∙ y) ≡ f x ∙ f y) →
    Σ[ g ∈ (A → B) ] Σ[ p ∈ (b ≡ g a) ] ((q : a ≡ a) → p ∙ cong g q ≡ f q ∙ p)
  deloopMorphism {ℓ} {ℓ'} {A} {B} Aconn Bgrpd {a} {b} f morph = g , pr , lemma1 where
    C : A → Type (ℓ-max ℓ ℓ')
    C x = Σ[ y ∈ B ] Σ[ p ∈ ((a ≡ x) → (b ≡ y)) ] ((ω : a ≡ a) (α : a ≡ x) → p (ω ∙ α) ≡ f ω ∙ p α)

    fRefl : f refl ≡ refl
    fRefl = reflUnique (f refl) (f refl) (sym (cong f (rUnit refl) ∙ morph _ _)) where
      reflUnique : (p : b ≡ b) (q : b ≡ b) → (p ∙ q ≡ q) → p ≡ refl
      reflUnique p q r = rUnit p ∙ cong (λ x → p ∙ x) (sym (rCancel q)) ∙ assoc _ _ _ ∙ cong (λ x → x ∙ q ⁻¹) r ∙ rCancel q

    isContrCa : isContr (C a)
    isContrCa = transport (cong isContr (sym (ua lemma))) isContrUnit where
      lemma : C a ≃ Unit {ℓ-max ℓ ℓ'}
      lemma =
        C a
          ≃⟨ isoToEquiv
            (iso
              (λ (y , p , !) → y , p , λ ω → cong p (rUnit ω) ∙ ! ω refl)
              (λ (y , p!) → y , fst p! , λ ω α → snd p! (ω ∙ α) ∙ cong (λ y → y ∙ (fst p! refl)) (morph ω α) ∙ sym (assoc _ _ _) ∙
                cong (λ y → f ω ∙ y) (sym (snd p! α)))
              (λ (y , p!) → ΣPathP (refl , Σ≡Prop (λ p → isPropΠ λ ω → Bgrpd _ _ _ _) refl))
              λ (y , p , !) → ΣPathP (refl , Σ≡Prop (λ p → isPropΠ2 λ _ _ → Bgrpd _ _ _ _) refl)
            ) ⟩
        (Σ[ y ∈ B ] Σ[ p ∈ ((a ≡ a) → (b ≡ y)) ] ((ω : a ≡ a) → p ω ≡ f ω ∙ p refl))
          ≃⟨ isoToEquiv
            (iso
              (λ (y , p , !) → y , p refl)
              (λ (y , prefl) → y , (λ ω → f ω ∙ prefl) , λ ω → cong (λ x → f ω ∙ x) (lUnit prefl) ∙ cong (λ x → f ω ∙ x ∙ prefl) (sym fRefl))
              (λ (y , prefl) → ΣPathP (refl , cong (λ x → x ∙ prefl) fRefl ∙ sym (lUnit prefl)))
              λ (y , p , !) → ΣPathP (refl , Σ≡Prop (λ _ → isPropΠ λ _ → Bgrpd _ _ _ _) (funExt λ ω → sym (! ω)))
            ) ⟩
        (Σ[ y ∈ B ] b ≡ y)
          ≃⟨ isoToEquiv (iso (λ _ → tt) (λ _ → b , refl) (λ { tt → refl }) λ (y , p) → ΣPathP (p , transport (sym (PathP≡compPathR _ _ _)) (sym (lUnit p)))) ⟩
        Unit ■
        
    isContrC : (x : A) → isContr (C x)
    isContrC x = recPropTrunc isPropIsContr (λ p → transport (cong isContr (cong C p)) isContrCa) (Aconn a x)

    g : A → B
    g x = fst (fst (isContrC x))

    p : (x : A) → a ≡ x → b ≡ g x
    p x = fst (snd (fst (isContrC x)))
    pr = p a refl

    ! : (x : A) → (ω : a ≡ a) (α : a ≡ x) → p x (ω ∙ α) ≡ f ω ∙ p x α
    ! x = snd (snd (fst (isContrC x)))
  
    lemma0 : (x : A) (α : a ≡ x) (x' : A) → (q : x ≡ x') → p x α ∙ cong g q ≡ p x' (α ∙ q)
    lemma0 x α x' q = J (λ x' q → p x α ∙ cong g q ≡ p x' (α ∙ q)) (sym (rUnit _) ∙ cong (p x) (rUnit α)) q

    lemma1 : (q : a ≡ a) → pr ∙ cong g q ≡ f q ∙ pr
    lemma1 q = lemma0 a refl a q ∙ cong (p a) (sym (lUnit _) ∙ rUnit _) ∙ ! a q refl

{-

PointedConnectedGroupoid : (ℓ : Level) → Type (ℓ-suc ℓ)
PointedConnectedGroupoid ℓ = Σ[ X ∈ Type ℓ ] Σ[ a ∈ X ] ((x : X) → ∥ a ≡ x ∥) × isGroupoid X
isConnPointedConnectedGroupoid : ∀ {ℓ} → (X : PointedConnectedGroupoid ℓ) → (x y : fst X) → ∥ x ≡ y ∥
isConnPointedConnectedGroupoid (X , a , conn , grpd) x y =
  recPropTrunc propTruncIsProp (λ p → recPropTrunc propTruncIsProp (λ q → ∣ sym p ∙ q ∣) (conn y)) (conn x)

pnt : ∀ {ℓ} (X : PointedConnectedGroupoid ℓ) → fst X
pnt X = fst (snd X)
  
deloopMorphGrpd : ∀ {ℓ} {ℓ'} {A : PointedConnectedGroupoid ℓ} {B : PointedConnectedGroupoid ℓ'}
    (f : pnt A ≡ pnt A → pnt B ≡ pnt B) → ((x y : pnt A ≡ pnt A) → f (x ∙ y) ≡ f x ∙ f y) →
    Σ[ g ∈ (fst A → fst B) ] Σ[ p ∈ (pnt B ≡ g (pnt A)) ] ((q : pnt A ≡ pnt A) → p ∙ cong g q ≡ f q ∙ p)
deloopMorphGrpd {ℓ} {ℓ'} {A} {B} f morph =
  deloopMorphism (isConnPointedConnectedGroupoid A) (snd (snd (snd B))) f morph

deloopEquiv : ∀ {ℓ} {ℓ'} {A : PointedConnectedGroupoid ℓ} {B : PointedConnectedGroupoid ℓ'}
  (f : pnt A ≡ pnt A → pnt B ≡ pnt B) (morph : (x y : pnt A ≡ pnt A) → f (x ∙ y) ≡ f x ∙ f y) → isEquiv f → isEquiv (fst (deloopMorphGrpd {A = A} {B = B} f morph))
deloopEquiv {ℓ} {ℓ'} {A} {B} f morph equiv-f = isEmbedding×isSurjection→isEquiv (isEmbedding-g , isSurjection-g) where
  deloop = deloopMorphGrpd {A = A} {B = B} f morph
  a = fst (snd A)
  b = fst (snd B)
  g : fst A → fst B
  g = fst deloop
  p : b ≡ g a
  p = fst (snd deloop)
  carac = snd (snd deloop)

  conn = fst (snd (snd A))

  equiv-lemma : isEquiv (λ q → p ∙ cong g q ∙ sym p)
  equiv-lemma = transport (cong isEquiv (funExt λ q →
    f q
      ≡⟨ rUnit (f q) ∙ cong (λ y → f q ∙ y) (sym (rCancel p)) ∙ assoc _ _ _ ⟩
    (f q ∙ p) ∙ sym p
      ≡⟨ cong (λ y → y ∙ sym p) (sym (carac q)) ∙ sym (assoc _ _ _) ⟩
    p ∙ cong g q ∙ sym p ∎
    )) equiv-f

  isEquiv-cong-g : isEquiv (cong {x = a} {y = a} g)
  isEquiv-cong-g = transport (cong isEquiv pre-cong-g≡g) (snd pre-cong-g) where
    pre-cong-g =
      compEquiv (compEquiv ((λ q → p ∙ cong g q ∙ sym p) , equiv-lemma) ((λ r → r ∙ p) , compPathr-isEquiv p)) ((λ r → sym p ∙ r) , compPathl-isEquiv (sym p))
    pre-cong-g≡g : equivFun pre-cong-g ≡ cong g
    pre-cong-g≡g = funExt λ q →
      sym p ∙ (p ∙ cong g q ∙ sym p) ∙ p
        ≡⟨ assoc _ _ _ ∙ cong (λ r → r ∙ p) (compPathl-cancel (sym p) _) ⟩
      (cong g q ∙ sym p) ∙ p
        ≡⟨ compPathr-cancel p _ ⟩
      cong g q ∎

  isEmbedding-g : isEmbedding g
  isEmbedding-g x y = recPropTrunc (isPropIsEquiv _) (λ r₁ → recPropTrunc (isPropIsEquiv _) (λ r₂ →
    transport (λ i → isEquiv (cong {x = r₁ i} {y = r₂ i} g)) isEquiv-cong-g)(conn y)) (conn x)

  isSurjection-g : isSurjection g
  isSurjection-g y = recPropTrunc propTruncIsProp (λ q → ∣ a , sym p ∙ q ∣) (fst (snd (snd B)) y)
-}
