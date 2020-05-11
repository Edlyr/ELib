{-# OPTIONS --cubical #-}

module ELib.B1.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Homotopy.Loopspace
open import ELib.Group.Base

PathP≡compPath2 : ∀ {ℓ} {A : Type ℓ} {a₀₀ a₁₀ : A} (a₋₀ : a₀₀ ≡ a₁₀) {a₀₁ a₁₁ : A} (a₋₁ : a₀₁ ≡ a₁₁) (a₀₋ : a₀₀ ≡ a₀₁) (a₁₋ : a₁₀ ≡ a₁₁)
  → (Square _ _ _ _ ≡ (a₀₋ ∙ a₋₁ ≡ a₋₀ ∙ a₁₋))
PathP≡compPath2 {ℓ} {A} {a₀₀} {a₁₀} =
  J (λ a₁₀ a₋₀ → {a₀₁ a₁₁ : A} → ((a₋₁ : a₀₁ ≡ a₁₁) (a₀₋ : a₀₀ ≡ a₀₁) (a₁₋ : a₁₀ ≡ a₁₁) → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋ ≡ (a₀₋ ∙ a₋₁ ≡ a₋₀ ∙ a₁₋)))
  λ a₋₁ a₀₋ a₁₋ → PathP≡compPath _ _ _ ∙ cong (λ y → _ ≡ y) (lUnit a₁₋)
    
module B {ℓ : Level} (Ggrp : Group ℓ) where
  module G = Group Ggrp
  _⨀_ = G.comp
  data B : Type ℓ where
    base : B
    path : G.type → base ≡ base
    id : path G.id ≡ refl
    conc : (g h h' g' : G.type) → (g ⨀ h) ≡ (h' ⨀ g') → Square (path g) (path g') (path h') (path h) --PathP (λ i → path h' i ≡ path h i) (path g) (path g')
    groupoid : (p q : base ≡ base) (r s : p ≡ q) → r ≡ s

  conc' : (g h : G.type) → path g ∙ path h ≡ path (g ⨀ h)
  conc' g h = transport (PathP≡compPath2 _ _ _ _) (conc g h G.id (g ⨀ h) (G.lUnit _)) ∙ sym (lUnit _ ∙ cong (λ x → x ∙ path (g ⨀ h)) (sym id))


  recB : ∀ {ℓ'} → {A : Type ℓ'} →
    (a : A) →
    (p : G.type → a ≡ a) →
    (idA : p G.id ≡ refl) →
    (concA : (g h h' g' : G.type) (eq : g ⨀ h ≡ h' ⨀ g') → Square (p g) (p g') (p h') (p h)) →
    (grpdA : (p q : a ≡ a) → (r s : p ≡ q) → r ≡ s) →
    B → A
  recB a pA idA concA grpdA base = a
  recB a pA idA concA grpdA (path g i) = pA g i
  recB a pA idA concA grpdA (id i j) = idA i j
  recB a pA idA concA grpdA (conc g h h' g' eq i j) = concA g h h' g' eq i j
  recB a pA idA concA grpdA (groupoid p q r s i j k) = grpdA (X p) (X q) (cong X r) (cong X s) i j k where
    X = cong (recB a pA idA concA grpdA)

  elimBSet : ∀ {ℓ'} → {A : B → Type ℓ'} → ((b : B) → isSet (A b)) → (a : A base) → ((g : G.type) → PathP (λ i → A (path g i)) a a) → (b : B) → A b
  elimBSet {ℓ'} {A} set a pA base = a
  elimBSet {ℓ'} {A} set a pA (path g i) = pA g i
  elimBSet {ℓ'} {A} set a pA (id i j) = isOfHLevel→isOfHLevelDep 2 set a a (cong (elimBSet set a pA) (path G.id)) refl id i j
  elimBSet {ℓ'} {A} set a pA (conc g h h' g' eq i j) = lemma i j where
    lemma : SquareP (λ i j → A (conc g h h' g' eq i j)) (pA g) (pA g') (pA h') (pA h)
    lemma = toPathP (subLemma _ _) where
      subLemma : isProp (PathP (λ i → A (path g' i)) a a)
      subLemma = isOfHLevelPathP' 1 (λ i → set (path g' i)) a a
  elimBSet {ℓ'} {A} set a pA (groupoid p q r s i j k) = isOfHLevel→isOfHLevelDep 3 (λ b → isSet→isGroupoid (set b)) a a
    (cong f p) (cong f q) (cong (cong f) r) (cong (cong f) s) (groupoid p q r s) i j k where
    f = elimBSet {ℓ'} {A} set a pA

  elimBProp : ∀ {ℓ'} → {A : B → Type ℓ'} → ((b : B) → isProp (A b)) → A base → (b : B) → A b
  elimBProp prop a = elimBSet (λ b → isProp→isSet (prop b)) a λ g → toPathP (prop _ _ _)

  isConnectedB : (x : B) → ∥ base ≡ x ∥
  isConnectedB = elimBProp (λ _ → propTruncIsProp) ∣ refl ∣

  isGroupoidB : isGroupoid B
  isGroupoidB x y = recPropTrunc isPropIsSet (λ p → recPropTrunc isPropIsSet
    (λ q → transport (λ i → isSet (Path B (p i) (q i))) groupoid)
    (isConnectedB y)) (isConnectedB x)
  Code : B → Type ℓ
  Code = recB
    G.type
    (λ g → isoToPath (iso
      (λ x → x ⨀ g)
      (λ x → x ⨀ G.inv g)
      (λ x → G.assoc _ _ _ ∙ cong (λ y → x ⨀ y) (G.lCancel g) ∙ sym (G.rUnit x))
      (λ x → G.assoc _ _ _ ∙ cong (λ y → x ⨀ y) (G.rCancel g) ∙ sym (G.rUnit x))
    ))
    (cong ua (equivEq _ _ (funExt λ x → sym (G.rUnit x))) ∙ uaIdEquiv)
    (λ g h h' g' eq → transport (sym (PathP≡compPath2 _ _ _ _)) (sym (uaCompEquiv _ _) ∙ cong ua (equivEq _ _ (funExt λ x →
      G.assoc _ _ _ ∙ cong (λ y → x ⨀ y) eq ∙ sym (G.assoc _ _ _)
    )) ∙ (uaCompEquiv _ _)))
    (λ p q r s → isOfHLevel≡ 2 G.set G.set p q r s)

  transport→ : ∀ {ℓ} (A : Type ℓ) (B C : A → Type ℓ) (a a' : A) (p : a ≡ a') (f : B a → C a) →
    transport (λ i → B (p i) → C (p i)) f ≡ λ x → transport (λ i → C (p i)) (f (transport (λ i → B (p (~ i))) x))
  transport→ A B C a a' p = J
    (λ a' p → (f : B a → C a) → transport (λ i → B (p i) → C (p i)) f ≡ λ x → transport (λ i → C (p i)) (f (transport (λ i → B (p (~ i))) x)))
    (λ f → transportRefl f ∙ funExt λ x → sym (transportRefl _ ∙ cong f (transportRefl _)))
    p
  transport≡p : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : y ≡ z) (q : x ≡ y) → transport (λ i → x ≡ (p i)) q ≡ q ∙ p
  transport≡p {ℓ} {A} {x} p q = J (λ C p → transport (λ i → x ≡ (p i)) q ≡ q ∙ p) (transportRefl q ∙ rUnit q) p

  transport≡pathToEquiv : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → transport p ≡ fst (pathToEquiv p)
  transport≡pathToEquiv p = funExt λ x → refl

  private
    encode : (b : B) → base ≡ b → Code b
    encode b p = transport (cong Code p) G.id
  
    decodeType : (b : B) → Type ℓ
    decodeType b = Code b → base ≡ b

    decodeTypeSet : (b : B) → isSet (decodeType b)
    decodeTypeSet b = isSetΠ λ _ → isGroupoidB _ _

    abstract
      decodePath : (g : G.type) → PathP (λ i → decodeType (path g i)) path path
      decodePath g = toPathP (
               (transport (λ i → Code (path g i) → (base ≡ path g i)) path)
                 ≡⟨ transport→ B Code (λ x → base ≡ x) base base (path g) path ⟩
               ((λ x →
                 transport (λ i → base ≡ path g i) (path (transport (λ i → Code (path g (~ i))) x))))
                   ≡⟨ (funExt λ x → transport≡p (path g) (path (transport (λ i₁ → Code (path g (~ i₁))) x)) ∙
                     cong (λ y → path (y ⨀ G.inv g) ∙ path g) (transportRefl _) ∙
                     conc' _ _ ∙ cong path ((G.assoc _ _ _ ∙ cong (λ y → x ⨀ y) (G.lCancel g) ∙ (sym (G.rUnit x))))) ⟩
                 path ∎)

    decode : (b : B) → decodeType b
    decode = elimBSet decodeTypeSet path decodePath
 
    sec : (b : B) → (p : base ≡ b) → decode b (encode b p) ≡ p
    sec b = J (λ b p → decode b (encode b p) ≡ p) (cong path (transportRefl _) ∙ id)

    ret : (b : B) → (x : Code b) → encode b (decode b x) ≡ x
    ret = elimBProp (λ b → isPropΠ λ x → CodeSet b _ _) (λ x → transportRefl _ ∙ sym (G.lUnit x)) where
      CodeSet : (b : B) → isSet (Code b)
      CodeSet = elimBProp (λ _ → isPropIsSet) G.set

  ΩBG→∙G : Ω (B , base) →∙ (G.type , G.id)
  ΩBG→∙G = encode base , transportRefl G.id

  G→∙ΩBG : (G.type , G.id) →∙ Ω (B , base)
  G→∙ΩBG = decode base , id

  G≃ΩBG : G.type ≃ fst (Ω (B , base))
  G≃ΩBG = isoToEquiv (iso (decode base) (encode base) (sec base) (ret base))

  ΩBG≃G : fst (Ω (B , base)) ≃ G.type
  ΩBG≃G = invEquiv G≃ΩBG
