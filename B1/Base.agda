{-# OPTIONS --cubical #-}

module ELib.B1.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Homotopy.Loopspace
open import Cubical.Structures.Group
open import Cubical.Data.Sigma
open import ELib.UsefulLemmas

PathP≡compPath2 : ∀ {ℓ} {A : Type ℓ} {a₀₀ a₁₀ : A} (a₋₀ : a₀₀ ≡ a₁₀) {a₀₁ a₁₁ : A} (a₋₁ : a₀₁ ≡ a₁₁) (a₀₋ : a₀₀ ≡ a₀₁) (a₁₋ : a₁₀ ≡ a₁₁)
  → (Square _ _ _ _ ≡ (a₀₋ ∙ a₋₁ ≡ a₋₀ ∙ a₁₋))
PathP≡compPath2 {ℓ} {A} {a₀₀} {a₁₀} =
  J (λ a₁₀ a₋₀ → {a₀₁ a₁₁ : A} → ((a₋₁ : a₀₁ ≡ a₁₁) (a₀₋ : a₀₀ ≡ a₀₁) (a₁₋ : a₁₀ ≡ a₁₁) → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋ ≡ (a₀₋ ∙ a₋₁ ≡ a₋₀ ∙ a₁₋)))
  λ a₋₁ a₀₋ a₁₋ → PathP≡compPath _ _ _ ∙ cong (λ y → _ ≡ y) (lUnit a₁₋)


transport→ : ∀ {ℓ} (A : Type ℓ) (B C : A → Type ℓ) (a a' : A) (p : a ≡ a') (f : B a → C a) →
  transport (λ i → B (p i) → C (p i)) f ≡ λ x → transport (λ i → C (p i)) (f (transport (λ i → B (p (~ i))) x))
transport→ A B C a a' p = J
  (λ a' p → (f : B a → C a) → transport (λ i → B (p i) → C (p i)) f ≡ λ x → transport (λ i → C (p i)) (f (transport (λ i → B (p (~ i))) x)))
  (λ f → transportRefl f ∙ funExt λ x → sym (transportRefl _ ∙ cong f (transportRefl _)))
  p
transport→R : ∀ {ℓ} (A B : Type ℓ) (C : A → Type ℓ) (a a' : A) (p : a ≡ a') (f : B → C a) →
  transport (λ i → B → C (p i)) f ≡ λ x → transport (λ i → C (p i)) (f x)
transport→R A B C a a' p f = transport→ A (λ _ → B) C a a' p f ∙ funExt λ x → cong (λ y → transport (cong C p) y) (cong f (transportRefl x))

transport≡p : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : y ≡ z) (q : x ≡ y) → transport (λ i → x ≡ (p i)) q ≡ q ∙ p
transport≡p {ℓ} {A} {x} p q = J (λ C p → transport (λ i → x ≡ (p i)) q ≡ q ∙ p) (transportRefl q ∙ rUnit q) p

--transport≡pathToEquiv : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → transport p ≡ fst (pathToEquiv p)
--transport≡pathToEquiv p = funExt λ x → refl

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
              (λ (y , p!) → ΣPathP (refl , ΣProp≡ (λ p → isPropΠ λ ω → Bgrpd _ _ _ _) refl))
              λ (y , p , !) → ΣPathP (refl , ΣProp≡ (λ p → isPropΠ2 λ _ _ → Bgrpd _ _ _ _) refl)
            ) ⟩
        (Σ[ y ∈ B ] Σ[ p ∈ ((a ≡ a) → (b ≡ y)) ] ((ω : a ≡ a) → p ω ≡ f ω ∙ p refl))
          ≃⟨ isoToEquiv
            (iso
              (λ (y , p , !) → y , p refl)
              (λ (y , prefl) → y , (λ ω → f ω ∙ prefl) , λ ω → cong (λ x → f ω ∙ x) (lUnit prefl) ∙ cong (λ x → f ω ∙ x ∙ prefl) (sym fRefl))
              (λ (y , prefl) → ΣPathP (refl , cong (λ x → x ∙ prefl) fRefl ∙ sym (lUnit prefl)))
              λ (y , p , !) → ΣPathP (refl , ΣProp≡ (λ _ → isPropΠ λ _ → Bgrpd _ _ _ _) (funExt λ ω → sym (! ω)))
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

    --result : PathP (λ i → a ≡ a → pr i ≡ pr i) f (cong g)
    --result = {!toPathP!}

module B {ℓ : Level} (Ggrp : Group {ℓ}) where
  module G = GroupLemmas Ggrp
  _⨀_ = G.op
  data B : Type ℓ where
    base : B
    path : G.type → base ≡ base
    conc : (g h : G.type) → Square (path g) (path (g ⨀ h)) refl (path h)
    groupoid : (p q : base ≡ base) (r s : p ≡ q) → r ≡ s

  conc' : (g h : G.type) → path g ∙ path h ≡ path (g ⨀ h)
  conc' g h = transport (PathP≡compPathR _ _ _) (conc g h)

  id : path G.id ≡ refl
  id = L.idUniqueL (path G.id) (path G.id) ((transport (PathP≡compPathR _ _ _) (conc G.id G.id)) ∙ cong path (sym (G.lUnit G.id))) where
    loopspace : Group {ℓ}
    loopspace = (base ≡ base) , _∙_ , (groupoid , assoc) , refl , (λ x → sym (lUnit x)) , λ x → sym x , lCancel x
    module L = GroupLemmas loopspace

  recB : ∀ {ℓ'} → {A : Type ℓ'} →
    (a : A) →
    (p : G.type → a ≡ a) →
    (idA : p G.id ≡ refl) →
    (concA : (g h : G.type) → Square (p g) (p (g ⨀ h)) refl (p h))
    (grpdA : (p q : a ≡ a) → (r s : p ≡ q) → r ≡ s) →
    B → A
  recB a pA idA concA grpdA base = a
  recB a pA idA concA grpdA (path g i) = pA g i
  recB a pA idA concA grpdA (conc g h i j) = concA g h i j
  recB a pA idA concA grpdA (groupoid p q r s i j k) = grpdA (X p) (X q) (cong X r) (cong X s) i j k where
    X = cong (recB a pA idA concA grpdA)

  elimBSet : ∀ {ℓ'} → {A : B → Type ℓ'} → ((b : B) → isSet (A b)) → (a : A base) → ((g : G.type) → PathP (λ i → A (path g i)) a a) → (b : B) → A b
  elimBSet {ℓ'} {A} set a pA base = a
  elimBSet {ℓ'} {A} set a pA (path g i) = pA g i
  elimBSet {ℓ'} {A} set a pA (conc g h i j) = lemma i j where
    lemma : SquareP (λ i j → A (conc g h i j)) (pA g) (pA (g ⨀ h)) (λ i → a) (pA h)
    lemma = toPathP (subLemma _ _) where
      subLemma : isProp (PathP (λ i → A (path (g ⨀ h) i)) a a)
      subLemma = isOfHLevelPathP' 1 (λ i → set (path (g ⨀ h) i)) a a
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
    (λ g h → transport (sym (PathP≡compPathR _ _ _)) (sym (uaCompEquiv _ _) ∙ cong ua (equivEq _ _ (funExt λ x →
      G.assoc _ _ _))))
    (λ p q r s → isOfHLevel≡ 2 G.set G.set p q r s)

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
               (λ x → transport (λ i → base ≡ path g i) (path (transport (λ i → Code (path g (~ i))) x)))
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


module Test {ℓ : Level} (A : Type ℓ) (a : A) (grpd : isGroupoid A) (conn : (x y : A) → ∥ x ≡ y ∥) where
  G : Group {ℓ}
  G = (a ≡ a) , _∙_ , (grpd a a , assoc) , refl , (λ x → sym (lUnit x)) , λ x → (sym x) , lCancel x

  module BG = B G

  BG : Type ℓ
  BG = B.B G

  A→BG : _
  A→BG = deloopMorphism conn BG.isGroupoidB (fst BG.G→∙ΩBG) λ x y → sym (BG.conc' x y)

  --BG→A : _
  --BG→A = deloopMorphism (BG.elimBProp (λ _ → isPropΠ λ _ → propTruncIsProp) BG.isConnectedB) grpd (fst BG.ΩBG→∙G)
  --  λ x y → {!fst BG.ΩBG→∙G (x ∙ y)!} where

  {-isEquivCongBG→A : isEquiv (cong {x = a} {y = a} (fst A→BG))
  isEquivCongBG→A = {!!} where
    f = fst A→BG
    p : BG.base ≡ f a
    p = fst (snd A→BG)
    ! : (q : a ≡ a) → (p ∙ cong f q ≡ (fst BG.G→∙ΩBG q) ∙ p)
    ! = snd (snd A→BG)
    test0 : (q : a ≡ a) → cong f q ≡ sym p ∙ (fst BG.G→∙ΩBG q) ∙ p
    test0 q = sym (compPathl-cancel (sym p) _) ∙ cong (λ x → sym p ∙ x) (! q)
    test1 : cong f ≡ λ q → sym p ∙ (fst BG.G→∙ΩBG q) ∙ p
    test1 = funExt λ q → test0 q
    lama : {A B : Type ℓ} {f : A → B} {g : A → B} → (p : f ≡ g) → (x : A) → f x ≡ g x
    lama p x = λ i → p i x
    eq : isEquiv (test1 i1)
    eq = snd (isoToEquiv (iso (test1 i1) (λ q → (fst BG.ΩBG→∙G (p ∙ q ∙ sym p)))
      (λ q → cong (λ x → sym p ∙ x ∙ p) (pfff1 q) ∙ cong (λ x → sym p ∙ x) (sym (assoc _ _ _)) ∙ compPathl-cancel _ _ ∙ compPathr-cancel _ _)
      λ q → {!!}
      )) where
      pfff1 : (q : _) → fst BG.G→∙ΩBG (fst BG.ΩBG→∙G (p ∙ q ∙ sym p)) ≡ p ∙ q ∙ sym p
      pfff1 q = lama (cong fst (invEquiv-is-rinv BG.ΩBG≃G)) (p ∙ q ∙ sym p)
      pffff : (q : _) → (p ∙ (test1 i1 q) ∙ sym p) ≡ (fst BG.G→∙ΩBG q)
      pffff q = ? --{!cong (λ x → p ∙ x) ? ∙ ?!}
      --pfff2 : (q : _) → fst BG.ΩBG→∙G (p ∙ (test1 i1 q) ∙ sym p) ≡ fst BG.ΩBG→∙G (fst BG.G→∙ΩBG q)
      --pfff2 q = {!!} -- cong (fst BG.ΩBG→∙G) ?
      pfff3 : (q : _) → fst BG.ΩBG→∙G (fst BG.G→∙ΩBG q) ≡ q
      pfff3 = lama (cong fst (invEquiv-is-linv BG.ΩBG≃G))
    --test : PathP (λ i → a ≡ a → p i ≡ p i) (fst BG.G→∙ΩBG) (cong f)
    --test = toPathP (transport→R BG (a ≡ a) (λ x → x ≡ x) (p i0) (p i1) p (fst BG.G→∙ΩBG) ∙
    --  funExt λ q → fromPathP {A = λ i → p i ≡ p i} {x = fst BG.G→∙ΩBG q} (transport (sym (PathP≡compPath2 _ _ _ _)) (sym (! q))))
    --ok : isEquiv (fst BG.G→∙ΩBG)
    --ok = snd BG.G≃ΩBG-}
