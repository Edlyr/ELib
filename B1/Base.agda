{-# OPTIONS --cubical #-}

module ELib.B1.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Homotopy.Loopspace
open import Cubical.Structures.Group
open import Cubical.Data.Sigma
open import ELib.B1.MorphismDelooping
open import ELib.UsefulLemmas

PathP≡compPath2 : ∀ {ℓ} {A : Type ℓ} {a₀₀ a₁₀ : A} (a₋₀ : a₀₀ ≡ a₁₀) {a₀₁ a₁₁ : A} (a₋₁ : a₀₁ ≡ a₁₁) (a₀₋ : a₀₀ ≡ a₀₁) (a₁₋ : a₁₀ ≡ a₁₁)
  → (Square _ _ _ _ ≡ (a₀₋ ∙ a₋₁ ≡ a₋₀ ∙ a₁₋))
PathP≡compPath2 {ℓ} {A} {a₀₀} {a₁₀} =
  J (λ a₁₀ a₋₀ → {a₀₁ a₁₁ : A} → ((a₋₁ : a₀₁ ≡ a₁₁) (a₀₋ : a₀₀ ≡ a₀₁) (a₁₋ : a₁₀ ≡ a₁₁) → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋ ≡ (a₀₋ ∙ a₋₁ ≡ a₋₀ ∙ a₁₋)))
  λ a₋₁ a₀₋ a₁₋ → PathP≡compPath _ _ _ ∙ cong (λ y → _ ≡ y) (lUnit a₁₋)

transport≡p : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : y ≡ z) (q : x ≡ y) → transport (λ i → x ≡ (p i)) q ≡ q ∙ p
transport≡p {ℓ} {A} {x} p q = J (λ C p → transport (λ i → x ≡ (p i)) q ≡ q ∙ p) (transportRefl q ∙ rUnit q) p

--transport≡pathToEquiv : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → transport p ≡ fst (pathToEquiv p)
--transport≡pathToEquiv p = funExt λ x → refl

module B {ℓ : Level} (G : Group {ℓ}) where
  module G = Group G
  _⨀_ = G._+_
  inv = G.-_
  data B : Type ℓ where
    base : B
    path : ⟨ G ⟩ → base ≡ base
    conc : (g h : ⟨ G ⟩) → Square (path g) (path (g ⨀ h)) refl (path h)
    groupoid : (p q : base ≡ base) (r s : p ≡ q) → r ≡ s

  conc' : (g h : ⟨ G ⟩) → path g ∙ path h ≡ path (g ⨀ h)
  conc' g h = transport (PathP≡compPathR _ _ _) (conc g h)

  id : path G.0g ≡ refl
  id = L.idUniqueL (path G.0g) ((transport (PathP≡compPathR _ _ _) (conc G.0g G.0g)) ∙ cong path (G.lid G.0g)) where
    loopspace : Group {ℓ}
    loopspace = makeGroup (refl {x = base}) _∙_ sym groupoid assoc (λ x → sym (rUnit x)) (λ x → sym (lUnit x)) rCancel lCancel
    module L = GroupLemmas loopspace

  recB : ∀ {ℓ'} → {A : Type ℓ'} →
    (a : A) →
    (p : ⟨ G ⟩ → a ≡ a) →
    (idA : p G.0g ≡ refl) →
    (concA : (g h : ⟨ G ⟩) → Square (p g) (p (g ⨀ h)) refl (p h))
    (grpdA : (p q : a ≡ a) → (r s : p ≡ q) → r ≡ s) →
    B → A
  recB a pA idA concA grpdA base = a
  recB a pA idA concA grpdA (path g i) = pA g i
  recB a pA idA concA grpdA (conc g h i j) = concA g h i j
  recB a pA idA concA grpdA (groupoid p q r s i j k) = grpdA (X p) (X q) (cong X r) (cong X s) i j k where
    X = cong (recB a pA idA concA grpdA)

  elimBSet : ∀ {ℓ'} → {A : B → Type ℓ'} → ((b : B) → isSet (A b)) → (a : A base) → ((g : ⟨ G ⟩) → PathP (λ i → A (path g i)) a a) → (b : B) → A b
  elimBSet {ℓ'} {A} set a pA base = a
  elimBSet {ℓ'} {A} set a pA (path g i) = pA g i
  elimBSet {ℓ'} {A} set a pA (conc g h i j) = lemma i j where
    lemma : SquareP (λ i j → A (conc g h i j)) (pA g) (pA (g ⨀ h)) (λ i → a) (pA h)
    lemma = toPathP (subLemma _ _) where
      subLemma : isProp (PathP (λ i → A (path (g ⨀ h) i)) a a)
      subLemma = isOfHLevelPathP' 1 (set _) a a
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
    ⟨ G ⟩
    (λ g → isoToPath (iso
      (λ x → x ⨀ g)
      (λ x → x ⨀ inv g)
      (λ x → sym (G.assoc _ _ _) ∙ cong (λ y → x ⨀ y) (G.invl g) ∙ (G.rid x))
      (λ x → sym (G.assoc _ _ _) ∙ cong (λ y → x ⨀ y) (G.invr g) ∙ (G.rid x))
    ))
    (cong ua (equivEq _ _ (funExt λ x → (G.rid x))) ∙ uaIdEquiv)
    (λ g h → transport (sym (PathP≡compPathR _ _ _)) (sym (uaCompEquiv _ _) ∙ cong ua (equivEq _ _ (funExt λ x →
      sym (G.assoc _ _ _)))))
    (λ p q r s → isOfHLevel≡ 2 G.is-set G.is-set p q r s)

  private
    encode : (b : B) → base ≡ b → Code b
    encode b p = transport (cong Code p) G.0g
  
    decodeType : (b : B) → Type ℓ
    decodeType b = Code b → base ≡ b

    decodeTypeSet : (b : B) → isSet (decodeType b)
    decodeTypeSet b = isSetΠ λ _ → isGroupoidB _ _

    abstract
      decodePath : (g : ⟨ G ⟩) → PathP (λ i → decodeType (path g i)) path path
      decodePath g = toPathP (
               (transport (λ i → Code (path g i) → (base ≡ path g i)) path)
                 ≡⟨ transport→ B Code (λ x → base ≡ x) base base (path g) path ⟩
               (λ x → transport (λ i → base ≡ path g i) (path (transport (λ i → Code (path g (~ i))) x)))
                 ≡⟨ (funExt λ x → transport≡p (path g) (path (transport (λ i₁ → Code (path g (~ i₁))) x)) ∙
                    cong (λ y → path (y ⨀ inv g) ∙ path g) (transportRefl _) ∙
                    conc' _ _ ∙ cong path ((sym (G.assoc _ _ _) ∙ cong (λ y → x ⨀ y) (G.invl g) ∙ (G.rid x)))) ⟩
               path ∎)

    decode : (b : B) → decodeType b
    decode = elimBSet decodeTypeSet path decodePath
 
    sec : (b : B) → (p : base ≡ b) → decode b (encode b p) ≡ p
    sec b = J (λ b p → decode b (encode b p) ≡ p) (cong path (transportRefl _) ∙ id)

    ret : (b : B) → (x : Code b) → encode b (decode b x) ≡ x
    ret = elimBProp (λ b → isPropΠ λ x → CodeSet b _ _) (λ x → transportRefl _ ∙ (G.lid x)) where
      CodeSet : (b : B) → isSet (Code b)
      CodeSet = elimBProp (λ _ → isPropIsSet) G.is-set

  ΩBG→∙G : Ω (B , base) →∙ (⟨ G ⟩ , G.0g)
  ΩBG→∙G = encode base , transportRefl G.0g

  G→∙ΩBG : (⟨ G ⟩ , G.0g) →∙ Ω (B , base)
  G→∙ΩBG = decode base , id

  G≃ΩBG : ⟨ G ⟩ ≃ fst (Ω (B , base))
  G≃ΩBG = isoToEquiv (iso (decode base) (encode base) (sec base) (ret base))

  ΩBG≃G : fst (Ω (B , base)) ≃ ⟨ G ⟩
  ΩBG≃G = invEquiv G≃ΩBG


module Test {ℓ : Level} (A : Type ℓ) (a : A) (grpd : isGroupoid A) (conn : (x y : A) → ∥ x ≡ y ∥) where
  G : Group {ℓ}
  G = makeGroup (refl {x = a}) _∙_ sym (grpd a a) assoc (λ x → sym (rUnit x)) (λ x → sym (lUnit x)) rCancel lCancel

  module BG = B G

  BG : Type ℓ
  BG = B.B G

  A→BG : _
  A→BG = Delooping.deloop conn BG.isGroupoidB (fst BG.G→∙ΩBG) λ x y → sym (BG.conc' x y)

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
