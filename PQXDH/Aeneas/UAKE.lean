/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Extracted.Pqxdh
import PQXDH.Spec.Basic
import PQXDH.Spec.UAKE
import PQXDH.ToVCVio.CryptoFoundations.AKE.UAKE.Defs

/-!
# PQXDH as a UAKE, instantiated with the Aeneas-extracted implementation
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace PQXDH.Aeneas

noncomputable section

instance {α : Type} {n : Aeneas.Std.Usize} [DecidableEq α] :
    DecidableEq (Aeneas.Std.Array α n) :=
  inferInstanceAs (DecidableEq { l : List α // l.length = n.val })

instance : SampleableType Aeneas.Std.U8 :=
  SampleableType.ofEquiv (α := BitVec 8)
    ⟨fun bv => ⟨bv⟩, fun x => x.bv, fun _ => rfl, fun _ => rfl⟩

instance {α : Type} {n : Aeneas.Std.Usize} [SampleableType α] :
    SampleableType (Aeneas.Std.Array α n) :=
  inferInstanceAs (SampleableType (List.Vector α n.val))

abbrev Bytes (n : Aeneas.Std.Usize) : Type := Aeneas.Std.Array Aeneas.Std.U8 n

abbrev ECKey : Type := Bytes 32#usize

abbrev PQPK : Type := Bytes 1568#usize

abbrev PQSK : Type := Bytes 3168#usize

abbrev CT : Type := Bytes 1569#usize

abbrev SS : Type := Bytes 32#usize

abbrev Key : Type := Bytes 32#usize

abbrev Coins : Type := Bytes 32#usize

def getOk {α : Type} [Inhabited α] : Aeneas.Std.Result α → α
  | .ok x => x
  | _ => default

def deriveKeys (dh1 dh2 dh3 : ECKey) (dh4 : Option ECKey) (ss : SS) :
    Aeneas.Std.Result (Key × Key × Key) := do
  let okm ← match dh4 with
    | none => do
        let secretInput ← pqxdh.pqxdh_secret_input dh1 dh2 dh3 ss
        let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice secretInput)
        let s1 ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice pqxdh.PQXDH_LABEL)
        pqxdh.hkdf_sha256_derive s s1
    | some dh4 => do
        let secretInput ← pqxdh.pqxdh_secret_input_with_opk dh1 dh2 dh3 dh4 ss
        let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice secretInput)
        let s1 ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice pqxdh.PQXDH_LABEL)
        pqxdh.hkdf_sha256_derive s s1
  pqxdh.derive_split okm

def DeriveKeysTotal : Prop :=
  ∀ (dh1 dh2 dh3 : ECKey) (dh4 : Option ECKey) (ss : SS),
    ∃ ks, deriveKeys dh1 dh2 dh3 dh4 ss = .ok ks

variable {SPK SSK S C Msg IdC IdK : Type}

structure Parameters (SPK SSK S C Msg IdC IdK : Type) where
  ecKeygen : ProbComp pqxdh.KeyPair
  pqKeygen : ProbComp (PQPK × PQSK)
  encapsCoins : ProbComp Coins
  sig : SignatureAlg ProbComp (ECKey ⊕ PQPK) SPK SSK S
  aead : AEAD.Scheme ProbComp Msg Key (ECKey × ECKey × PQPK) C
  idEC : ECKey → IdC
  idKEM : PQPK → IdK

structure InitiatorParameters (SPK Msg : Type) where
  ikA : pqxdh.KeyPair
  ikB : ECKey
  sigpkB : SPK
  msg : Msg

structure RecipientIdentity (SPK SSK S : Type) where
  ikB : pqxdh.KeyPair
  sigkB : SPK × SSK
  spkB : pqxdh.KeyPair
  spkSigB : S

structure RecipientParameters (SPK SSK S : Type) where
  ikB : pqxdh.KeyPair
  sigkB : SPK × SSK
  spkB : pqxdh.KeyPair
  spkSigB : S
  opkB : Option pqxdh.KeyPair
  pqpkB : PQPK × PQSK

def pqkem (P : Parameters SPK SSK S C Msg IdC IdK) :
    KEMScheme ProbComp SS PQPK PQSK CT where
  keygen := P.pqKeygen
  encaps := fun pk => do
    let coins ← P.encapsCoins
    match pqxdh.mlkem_encapsulate pk coins with
    | .ok (ss, ct) => return (ct, ss)
    | _ => return default
  decaps := fun sk ct =>
    match pqxdh.mlkem_decapsulate sk ct with
    | .ok ss => return some ss
    | _ => return none

def AgreeComm (P : Parameters SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ kp₁ ∈ support P.ecKeygen, ∀ kp₂ ∈ support P.ecKeygen,
    pqxdh.x25519_agree kp₁.private_key kp₂.public_key
      = pqxdh.x25519_agree kp₂.private_key kp₁.public_key

def AgreeTotal (P : Parameters SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ kp₁ ∈ support P.ecKeygen, ∀ kp₂ ∈ support P.ecKeygen,
    ∃ z, pqxdh.x25519_agree kp₁.private_key kp₂.public_key = .ok z

def EncapsTotal (P : Parameters SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ kp ∈ support P.pqKeygen, ∀ coins ∈ support P.encapsCoins,
    ∃ r, pqxdh.mlkem_encapsulate kp.1 coins = .ok r

def kdfPRF : PRFScheme SS (ECKey × ECKey × ECKey × Option ECKey) (Key × Key × Key) where
  keygen := $ᵗ SS
  eval := fun ss q => getOk (deriveKeys q.1 q.2.1 q.2.2.1 q.2.2.2 ss)

def kdfPRFDH (P : Parameters SPK SSK S C Msg IdC IdK) :
    PRFScheme pqxdh.KeyPair (ECKey × ECKey × Option ECKey × SS) (Key × Key × Key) where
  keygen := P.ecKeygen
  eval := fun kp q => getOk (deriveKeys q.1 q.2.1 kp.public_key q.2.2.1 q.2.2.2)

def DDHAdversary : Type := ECKey → ECKey → ECKey → ProbComp Bool

def ddhExpReal (P : Parameters SPK SSK S C Msg IdC IdK) (adversary : DDHAdversary) :
    ProbComp Bool := do
  let kpA ← P.ecKeygen
  let kpB ← P.ecKeygen
  adversary kpA.public_key kpB.public_key
    (getOk (pqxdh.x25519_agree kpA.private_key kpB.public_key))

def ddhExpRand (P : Parameters SPK SSK S C Msg IdC IdK) (adversary : DDHAdversary) :
    ProbComp Bool := do
  let kpA ← P.ecKeygen
  let kpB ← P.ecKeygen
  let kpC ← P.ecKeygen
  adversary kpA.public_key kpB.public_key kpC.public_key

noncomputable def ddhDistAdvantage (P : Parameters SPK SSK S C Msg IdC IdK)
    (adversary : DDHAdversary) : ℝ :=
  |(Pr[= true | ddhExpReal P adversary]).toReal -
    (Pr[= true | ddhExpRand P adversary]).toReal|

def genOPK (keygen : ProbComp pqxdh.KeyPair) (hasOPK : Bool) :
    ProbComp (Option pqxdh.KeyPair) :=
  if hasOPK then some <$> keygen else pure none

def setup (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) :
    ProbComp (InitiatorParameters SPK Msg × RecipientIdentity SPK SSK S) := do
  let ikA ← P.ecKeygen
  let ikB ← P.ecKeygen
  let sigkB ← P.sig.keygen
  let spkB ← P.ecKeygen
  let spkSigB ← P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)
  return ({ ikA := ikA, ikB := ikB.public_key, sigpkB := sigkB.1, msg := msg },
    { ikB := ikB, sigkB := sigkB, spkB := spkB, spkSigB := spkSigB })

def publish (P : Parameters SPK SSK S C Msg IdC IdK)
    (p : RecipientParameters SPK SSK S) :
    ProbComp (PreKeyBundle ECKey PQPK S IdC IdK) := do
  let pqpkSigB ← P.sig.sign p.sigkB.1 p.sigkB.2 (EncodeKEM p.pqpkB.1)
  return { ikB := p.ikB.public_key
           spkB := (p.spkB.public_key, P.idEC p.spkB.public_key)
           spkSigB := p.spkSigB
           pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
           pqpkSigB := pqpkSigB
           opkB := p.opkB.map fun opk => (opk.public_key, P.idEC opk.public_key) }

def initiate (P : Parameters SPK SSK S C Msg IdC IdK)
    (p : InitiatorParameters SPK Msg)
    (bundle : PreKeyBundle ECKey PQPK S IdC IdK) :
    ProbComp (Option (InitialMessage ECKey CT C IdC IdK ×
      SessionContext ECKey PQPK Msg Key)) := do
  if bundle.ikB ≠ p.ikB then return none
  let okSPK ← P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB
  let okPQPK ← P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB
  if !(okSPK && okPQPK) then return none
  let ekA ← P.ecKeygen
  let coins ← P.encapsCoins
  match pqxdh.pqxdh_initiate
      { our_identity_key_pair := p.ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := bundle.ikB
        their_signed_pre_key := bundle.spkB.1
        their_one_time_pre_key := bundle.opkB.map Prod.fst
        their_kyber_pre_key := bundle.pqpkB.1 } coins with
  | .ok agreement =>
      let SK := agreement.keys.root_key
      let KA := agreement.keys.chain_key
      let KB := agreement.keys.pqr_key
      let AD := (p.ikA.public_key, bundle.ikB, bundle.pqpkB.1)
      let ctxt ← P.aead.encrypt KA AD p.msg
      return some ({ ikA := p.ikA.public_key
                     ekA := ekA.public_key
                     ct := agreement.kyber_ciphertext
                     idSPK := bundle.spkB.2
                     idPQPK := bundle.pqpkB.2
                     idOPK := bundle.opkB.map Prod.snd
                     ctxt := ctxt },
        { sk := SK, kb := KB, ad := AD, msg := p.msg })
  | _ => return none

def accept [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (p : RecipientParameters SPK SSK S)
    (msg : InitialMessage ECKey CT C IdC IdK) :
    ProbComp (Option (SessionContext ECKey PQPK Msg Key)) := do
  if msg.idSPK ≠ P.idEC p.spkB.public_key ∨ msg.idPQPK ≠ P.idKEM p.pqpkB.1 ∨
      msg.idOPK ≠ p.opkB.map (fun opk => P.idEC opk.public_key) then return none
  match pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_secret_key := p.pqpkB.2
        their_identity_key := msg.ikA
        their_ephemeral_key := msg.ekA
        their_kyber_ciphertext := msg.ct } with
  | .ok (some keys) =>
      let AD := (msg.ikA, p.ikB.public_key, p.pqpkB.1)
      match P.aead.decrypt keys.chain_key AD msg.ctxt with
      | some m =>
          return some { sk := keys.root_key, kb := keys.pqr_key, ad := AD, msg := m }
      | none => return none
  | _ => return none

def confirm [DecidableEq Msg] (P : Parameters SPK SSK S C Msg IdC IdK)
    (ctx : SessionContext ECKey PQPK Msg Key) (conf : C) : Option Key :=
  if P.aead.decrypt ctx.kb ctx.ad conf = some ctx.msg then some ctx.sk
  else none

def initiator [DecidableEq Msg] (P : Parameters SPK SSK S C Msg IdC IdK) :
    Party ProbComp (InitiatorParameters SPK Msg)
      (Message ECKey PQPK CT S C IdC IdK) (Option Key) where
  State := InitiatorParameters SPK Msg ⊕ SessionContext ECKey PQPK Msg Key ⊕ Key
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiate P p b with
        | some (im, ctx) => pure (.acceptAndSend (.inr (.inl ctx)) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf =>
        match confirm P ctx conf with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr SK) => pure (some (some SK))
    | _ => pure none

def recipient [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity SPK SSK S)
      (Message ECKey PQPK CT S C IdC IdK) (Option Key) where
  State := RecipientParameters SPK SSK S ⊕ Key
  init := fun idn => do
    let opkB ← genOPK P.ecKeygen hasOPK
    let pqpkB ← P.pqKeygen
    let p : RecipientParameters SPK SSK S :=
      { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB, spkSigB := idn.spkSigB,
        opkB := opkB, pqpkB := pqpkB }
    let bundle ← publish P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← accept P p im with
        | some ctx => do
            let conf ← P.aead.encrypt ctx.kb ctx.ad ctx.msg
            pure (.acceptAndSend (.inr ctx.sk) (.confirmation conf) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

def uakeInitiator [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp Key (InitiatorParameters SPK Msg)
      (RecipientIdentity SPK SSK S)
      (Message ECKey PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiator P
  T := recipient P hasOPK

def uakeRecipient [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp Key (RecipientIdentity SPK SSK S)
      (InitiatorParameters SPK Msg)
      (Message ECKey PQPK CT S C IdC IdK) where
  rounds := 4
  setup := Prod.swap <$> setup P msg
  U := recipient P hasOPK
  T := initiator P

section CorrectnessLemmas

private lemma probOutput_probComp_evalDist {α : Type} (oa : ProbComp α) (x : α) :
    Pr[= x | ProbCompRuntime.probComp.evalDist oa] = Pr[= x | oa] := by
  rfl

private lemma support_eq_singleton_true_of_evalDist {oa : ProbComp Bool}
    (h : Pr[= true | ProbCompRuntime.probComp.evalDist oa] = 1) :
    support oa = {true} := by
  rw [probOutput_probComp_evalDist, probOutput_eq_one_iff] at h
  exact h.2

private lemma verify_eq_true_of_perfectlyComplete
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    {kp : SPK × SSK} (hkp : kp ∈ support P.sig.keygen)
    (m : ECKey ⊕ PQPK) {σ : S} (hσ : σ ∈ support (P.sig.sign kp.1 kp.2 m))
    {b : Bool} (hb : b ∈ support (P.sig.verify kp.1 m σ)) : b = true := by
  have h := support_eq_singleton_true_of_evalDist (hsig m)
  have hmem : b ∈ support (do
      let (pk, sk) ← P.sig.keygen
      let s ← P.sig.sign pk sk m
      P.sig.verify pk m s) := by
    refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
    exact (mem_support_bind_iff _ _ _).mpr ⟨σ, hσ, hb⟩
  rw [h] at hmem
  exact hmem

private lemma mlkem_decapsulate_eq_ok
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    {kp : PQPK × PQSK} (hkp : kp ∈ support P.pqKeygen)
    {coins : Coins} (hcoins : coins ∈ support P.encapsCoins)
    {ss : SS} {ct : CT} (henc : pqxdh.mlkem_encapsulate kp.1 coins = .ok (ss, ct)) :
    pqxdh.mlkem_decapsulate kp.2 ct = .ok ss := by
  have h := support_eq_singleton_true_of_evalDist hkem
  have hct : (ct, ss) ∈ support ((pqkem P).encaps kp.1) := by
    simp only [pqkem, mem_support_bind_iff]
    exact ⟨coins, hcoins, by simp [henc]⟩
  have key : ∀ r ∈ support ((pqkem P).decaps kp.2 ct), r = some ss := by
    intro r hr
    have hmem : decide (r = some ss) ∈ support ((pqkem P).CorrectExp) := by
      unfold KEMScheme.CorrectExp
      refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
      refine (mem_support_bind_iff _ _ _).mpr ⟨(ct, ss), hct, ?_⟩
      refine (mem_support_bind_iff _ _ _).mpr ⟨r, hr, ?_⟩
      simp
    rw [h] at hmem
    simpa using hmem
  cases hdec : pqxdh.mlkem_decapsulate kp.2 ct with
  | ok ss' =>
      have := key (some ss') (by simp [pqkem, hdec])
      simp only [Option.some.injEq] at this
      rw [this]
  | fail e =>
      have := key none (by simp [pqkem, hdec])
      simp at this
  | div =>
      have := key none (by simp [pqkem, hdec])
      simp at this

private lemma aead_decrypt_encrypt_of_perfectlyCorrect [DecidableEq Msg]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (k : Key) (ad : ECKey × ECKey × PQPK) (m : Msg) {c : C}
    (hc : c ∈ support (P.aead.encrypt k ad m)) :
    P.aead.decrypt k ad c = some m := by
  have h := haead m ad
  rw [probOutput_eq_one_iff] at h
  have hmem : decide (P.aead.decrypt k ad c = some m) ∈
      support (AEAD.CorrectExp P.aead m ad) := by
    unfold AEAD.CorrectExp
    refine (mem_support_bind_iff _ _ _).mpr ⟨k, mem_support_uniformSample Key, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨c, hc, ?_⟩
    simp
  rw [h.2] at hmem
  simpa using hmem

private lemma opkB_mem_of_genOPK {keygen : ProbComp pqxdh.KeyPair} {hasOPK : Bool}
    {opkB : Option pqxdh.KeyPair}
    (h : opkB ∈ support (genOPK keygen hasOPK)) :
    ∀ x ∈ opkB, x ∈ support keygen := by
  unfold genOPK at h
  cases hasOPK with
  | false =>
      simp only [Bool.false_eq_true, if_false, support_pure, Set.mem_singleton_iff] at h
      subst h; simp
  | true =>
      simp only [if_true, support_map, Set.mem_image] at h
      obtain ⟨opk, hopk, rfl⟩ := h
      intro x hx
      simp only [Option.mem_def, Option.some.injEq] at hx
      exact hx ▸ hopk

private lemma pqxdh_accept_eq_of_initiate_eq_ok
    (ikA ekA ikB spkB : pqxdh.KeyPair) (opkB : Option pqxdh.KeyPair)
    (pqpk : PQPK) (pqsk : PQSK) (coins : Coins) (ag : pqxdh.InitiatorAgreement)
    (hdh1 : pqxdh.x25519_agree spkB.private_key ikA.public_key
      = pqxdh.x25519_agree ikA.private_key spkB.public_key)
    (hdh2 : pqxdh.x25519_agree ikB.private_key ekA.public_key
      = pqxdh.x25519_agree ekA.private_key ikB.public_key)
    (hdh3 : pqxdh.x25519_agree spkB.private_key ekA.public_key
      = pqxdh.x25519_agree ekA.private_key spkB.public_key)
    (hdh4 : ∀ opk ∈ opkB, pqxdh.x25519_agree opk.private_key ekA.public_key
      = pqxdh.x25519_agree ekA.private_key opk.public_key)
    (hkem : ∀ ss ct, pqxdh.mlkem_encapsulate pqpk coins = .ok (ss, ct) →
      pqxdh.mlkem_decapsulate pqsk ct = .ok ss)
    (hcanon : pqxdh.ec_is_canonical ekA.public_key = .ok true)
    (hI : pqxdh.pqxdh_initiate
      { our_identity_key_pair := ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := ikB.public_key
        their_signed_pre_key := spkB.public_key
        their_one_time_pre_key := opkB.map pqxdh.KeyPair.public_key
        their_kyber_pre_key := pqpk } coins = .ok ag) :
    pqxdh.pqxdh_accept
      { our_identity_key_pair := ikB
        our_signed_pre_key_pair := spkB
        our_one_time_pre_key_pair := opkB
        our_kyber_secret_key := pqsk
        their_identity_key := ikA.public_key
        their_ephemeral_key := ekA.public_key
        their_kyber_ciphertext := ag.kyber_ciphertext } = .ok (some ag.keys) := by
  unfold pqxdh.pqxdh_initiate at hI
  unfold pqxdh.pqxdh_accept
  simp only [Aeneas.Std.lift] at hI ⊢
  cases h1 : pqxdh.x25519_agree ikA.private_key spkB.public_key with
  | fail e => simp [h1] at hI
  | div => simp [h1] at hI
  | ok dh1 =>
  cases h2 : pqxdh.x25519_agree ekA.private_key ikB.public_key with
  | fail e => simp [h1, h2] at hI
  | div => simp [h1, h2] at hI
  | ok dh2 =>
  cases h3 : pqxdh.x25519_agree ekA.private_key spkB.public_key with
  | fail e => simp [h1, h2, h3] at hI
  | div => simp [h1, h2, h3] at hI
  | ok dh3 =>
  cases henc : pqxdh.mlkem_encapsulate pqpk coins with
  | fail e => simp [h1, h2, h3, henc] at hI
  | div => simp [h1, h2, h3, henc] at hI
  | ok ssct =>
  obtain ⟨ss, ct⟩ := ssct
  have hdec := hkem ss ct henc
  cases opkB with
  | none =>
      cases hsi : pqxdh.pqxdh_secret_input dh1 dh2 dh3 ss with
      | fail e => simp [h1, h2, h3, henc, hsi] at hI
      | div => simp [h1, h2, h3, henc, hsi] at hI
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [h1, h2, h3, henc, hsi, hokm] at hI
      | div => simp [h1, h2, h3, henc, hsi, hokm] at hI
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [h1, h2, h3, henc, hsi, hokm, hsplit] at hI
      | div => simp [h1, h2, h3, henc, hsi, hokm, hsplit] at hI
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp [h1, h2, h3, henc, hsi, hokm, hsplit] at hI
      subst hI
      simp [hcanon, hdh1, hdh2, hdh3, h1, h2, h3, hdec, hsi, hokm, hsplit]
  | some opk =>
      cases h4 : pqxdh.x25519_agree ekA.private_key opk.public_key with
      | fail e => simp [h1, h2, h3, henc, h4] at hI
      | div => simp [h1, h2, h3, henc, h4] at hI
      | ok dh4 =>
      cases hsi : pqxdh.pqxdh_secret_input_with_opk dh1 dh2 dh3 dh4 ss with
      | fail e => simp [h1, h2, h3, henc, h4, hsi] at hI
      | div => simp [h1, h2, h3, henc, h4, hsi] at hI
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [h1, h2, h3, henc, h4, hsi, hokm] at hI
      | div => simp [h1, h2, h3, henc, h4, hsi, hokm] at hI
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [h1, h2, h3, henc, h4, hsi, hokm, hsplit] at hI
      | div => simp [h1, h2, h3, henc, h4, hsi, hokm, hsplit] at hI
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp [h1, h2, h3, henc, h4, hsi, hokm, hsplit] at hI
      subst hI
      simp [hcanon, hdh1, hdh2, hdh3, hdh4 opk rfl, h1, h2, h3, h4, hdec, hsi, hokm, hsplit]

private lemma mem_support_initiate
    (P : Parameters SPK SSK S C Msg IdC IdK)
    {p : InitiatorParameters SPK Msg} {bundle : PreKeyBundle ECKey PQPK S IdC IdK}
    {r : Option (InitialMessage ECKey CT C IdC IdK × SessionContext ECKey PQPK Msg Key)}
    (hpin : bundle.ikB = p.ikB)
    (hok₁ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB),
      b = true)
    (hok₂ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB),
      b = true)
    (hr : r ∈ support (initiate P p bundle)) :
    r = none ∨
      ∃ ekA ∈ support P.ecKeygen, ∃ coins ∈ support P.encapsCoins,
      ∃ ag : pqxdh.InitiatorAgreement,
        pqxdh.pqxdh_initiate
          { our_identity_key_pair := p.ikA
            our_ephemeral_key_pair := ekA
            their_identity_key := p.ikB
            their_signed_pre_key := bundle.spkB.1
            their_one_time_pre_key := bundle.opkB.map Prod.fst
            their_kyber_pre_key := bundle.pqpkB.1 } coins = .ok ag ∧
      ∃ ctxt ∈ support (P.aead.encrypt ag.keys.chain_key
          (p.ikA.public_key, p.ikB, bundle.pqpkB.1) p.msg),
        r = some (⟨p.ikA.public_key, ekA.public_key, ag.kyber_ciphertext,
            bundle.spkB.2, bundle.pqpkB.2, bundle.opkB.map Prod.snd, ctxt⟩,
          ⟨ag.keys.root_key, ag.keys.pqr_key,
            (p.ikA.public_key, p.ikB, bundle.pqpkB.1), p.msg⟩) := by
  simp only [initiate, hpin, ne_eq, not_true_eq_false, if_false,
    mem_support_bind_iff] at hr
  obtain ⟨_, _, okSPK, hok, okPQPK, hok', hr⟩ := hr
  obtain rfl := hok₁ _ hok
  obtain rfl := hok₂ _ hok'
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false,
    mem_support_bind_iff] at hr
  obtain ⟨_, _, ekA, hekA, coins, hcoins, hr⟩ := hr
  cases hI : pqxdh.pqxdh_initiate
      { our_identity_key_pair := p.ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := p.ikB
        their_signed_pre_key := bundle.spkB.1
        their_one_time_pre_key := bundle.opkB.map Prod.fst
        their_kyber_pre_key := bundle.pqpkB.1 } coins with
  | ok ag =>
      rw [hI] at hr
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨ctxt, hctxt, rfl⟩ := hr
      exact Or.inr ⟨ekA, hekA, coins, hcoins, ag, hI, ctxt, hctxt, rfl⟩
  | fail e =>
      rw [hI] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      exact Or.inl hr
  | div =>
      rw [hI] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      exact Or.inl hr

private lemma accept_eq_pure_some
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    {p : RecipientParameters SPK SSK S} {im : InitialMessage ECKey CT C IdC IdK}
    {keys : pqxdh.HandshakeKeys} {m₀ : Msg}
    (hid₁ : im.idSPK = P.idEC p.spkB.public_key)
    (hid₂ : im.idPQPK = P.idKEM p.pqpkB.1)
    (hid₃ : im.idOPK = p.opkB.map (fun opk => P.idEC opk.public_key))
    (hacc : pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_secret_key := p.pqpkB.2
        their_identity_key := im.ikA
        their_ephemeral_key := im.ekA
        their_kyber_ciphertext := im.ct } = .ok (some keys))
    (hdec : P.aead.decrypt keys.chain_key (im.ikA, p.ikB.public_key, p.pqpkB.1) im.ctxt
      = some m₀) :
    accept P p im = pure (some ⟨keys.root_key, keys.pqr_key,
      (im.ikA, p.ikB.public_key, p.pqpkB.1), m₀⟩) := by
  simp [accept, hid₁, hid₂, hid₃, hacc, hdec]

private lemma accept_eq_pure_none
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    {p : RecipientParameters SPK SSK S} {im : InitialMessage ECKey CT C IdC IdK}
    (hacc : ∀ keys, pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_secret_key := p.pqpkB.2
        their_identity_key := im.ikA
        their_ephemeral_key := im.ekA
        their_kyber_ciphertext := im.ct } ≠ .ok (some keys)) :
    accept P p im = pure none := by
  cases hr : pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_secret_key := p.pqpkB.2
        their_identity_key := im.ikA
        their_ephemeral_key := im.ekA
        their_kyber_ciphertext := im.ct } with
  | ok o =>
      cases o with
      | none => simp [accept, hr]
      | some keys => exact absurd hr (hacc keys)
  | fail e => simp [accept, hr]
  | div => simp [accept, hr]

private lemma pqxdh_accept_ne_ok_some
    {rp : pqxdh.RecipientParameters} {res : Aeneas.Std.Result Bool}
    (hc : pqxdh.ec_is_canonical rp.their_ephemeral_key = res) (hres : res ≠ .ok true) :
    ∀ keys, pqxdh.pqxdh_accept rp ≠ .ok (some keys) := by
  intro keys h
  unfold pqxdh.pqxdh_accept at h
  rw [hc] at h
  cases res with
  | ok b =>
      cases b with
      | true => exact hres rfl
      | false => simp at h
  | fail e => simp at h
  | div => simp at h

private lemma run_support_initiator
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P)
    (msg : Msg)
    {ikA ikB spkB : pqxdh.KeyPair} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support P.ecKeygen)
    (hikB : ikB ∈ support P.ecKeygen)
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support P.ecKeygen)
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)))
    {uOut tOut : Option (Option Key)}
    (hrun : (uOut, tOut) ∈ support (Party.runHonest (initiator P) (recipient P hasOPK)
      ⟨ikA, ikB.public_key, sigkB.1, msg⟩ ⟨ikB, sigkB, spkB, spkSigB⟩ (3 + 1))) :
    uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join := by
  simp only [Party.runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, rfl, qInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₂, hσ₂, rfl⟩ := hbundle
  simp only [Party.InitResult.opening, Party.InitResult.state, mem_support_bind_iff] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [Party.runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  rcases mem_support_initiate P rfl
      (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hspkSigB hb)
      (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₂ hb) hir with
    rfl | ⟨ekA, hekA, coins, hcoins, ag, hI, ctxt, hctxt, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
    obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
    simp
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    dsimp only at hctxt hy
    simp only [mem_support_bind_iff] at hy
    obtain ⟨sr, ⟨ar, har, hsr⟩, hy⟩ := hy
    have hmap : Option.map Prod.fst
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map pqxdh.KeyPair.public_key opkB := by
      cases opkB <;> rfl
    rw [hmap] at hI
    have hidOPK : Option.map Prod.snd
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map (fun opk => P.idEC opk.public_key) opkB := by
      cases opkB <;> rfl
    cases hc : pqxdh.ec_is_canonical ekA.public_key with
    | ok b =>
      cases b with
      | true =>
        have hacc := pqxdh_accept_eq_of_initiate_eq_ok ikA ekA ikB spkB opkB
          pqpkB.1 pqpkB.2 coins ag
          (hdh spkB hspkB ikA hikA) (hdh ikB hikB ekA hekA) (hdh spkB hspkB ekA hekA)
          (fun opk hopk => hdh opk (hopkB opk hopk) ekA hekA)
          (fun ss ct h => mlkem_decapsulate_eq_ok P hkem hpqpkB hcoins h) hc hI
        have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
        rw [accept_eq_pure_some P rfl rfl hidOPK hacc hdecA] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsr
        obtain ⟨conf, hconf, rfl⟩ := hsr
        have hconfirm := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hconf
        simp only [confirm, hconfirm, reduceIte, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hy
        obtain ⟨x, rfl, hy⟩ := hy
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp
      | false =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp
    | fail e =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp
    | div =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp

private lemma run_support_recipient
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P)
    (msg : Msg)
    {ikA ikB spkB : pqxdh.KeyPair} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support P.ecKeygen)
    (hikB : ikB ∈ support P.ecKeygen)
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support P.ecKeygen)
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)))
    {uOut tOut : Option (Option Key)}
    (hrun : (uOut, tOut) ∈ support (Party.runHonest (recipient P hasOPK) (initiator P)
      ⟨ikB, sigkB, spkB, spkSigB⟩ ⟨ikA, ikB.public_key, sigkB.1, msg⟩ (4 + 1))) :
    uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join := by
  simp only [Party.runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, qInit, rfl, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₂, hσ₂, rfl⟩ := hbundle
  simp only [Party.InitResult.opening, Party.InitResult.state, mem_support_bind_iff] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [Party.runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  rcases mem_support_initiate P rfl
      (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hspkSigB hb)
      (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₂ hb) hir with
    rfl | ⟨ekA, hekA, coins, hcoins, ag, hI, ctxt, hctxt, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
    obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
    simp
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    dsimp only at hctxt hy
    simp only [mem_support_bind_iff] at hy
    obtain ⟨sr, ⟨ar, har, hsr⟩, hy⟩ := hy
    have hmap : Option.map Prod.fst
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map pqxdh.KeyPair.public_key opkB := by
      cases opkB <;> rfl
    rw [hmap] at hI
    have hidOPK : Option.map Prod.snd
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map (fun opk => P.idEC opk.public_key) opkB := by
      cases opkB <;> rfl
    cases hc : pqxdh.ec_is_canonical ekA.public_key with
    | ok b =>
      cases b with
      | true =>
        have hacc := pqxdh_accept_eq_of_initiate_eq_ok ikA ekA ikB spkB opkB
          pqpkB.1 pqpkB.2 coins ag
          (hdh spkB hspkB ikA hikA) (hdh ikB hikB ekA hekA) (hdh spkB hspkB ekA hekA)
          (fun opk hopk => hdh opk (hopkB opk hopk) ekA hekA)
          (fun ss ct h => mlkem_decapsulate_eq_ok P hkem hpqpkB hcoins h) hc hI
        have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
        rw [accept_eq_pure_some P rfl rfl hidOPK hacc hdecA] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsr
        obtain ⟨conf, hconf, rfl⟩ := hsr
        have hconfirm := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hconf
        simp only [confirm, hconfirm, reduceIte, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hy
        obtain ⟨x, rfl, hy⟩ := hy
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp
      | false =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp
    | fail e =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp
    | div =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp

end CorrectnessLemmas

theorem uakeInitiator_perfectlyCorrect
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) := by
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact probFailure_of_liftM_PMF _
  intro b hb
  simp only [UAKE.CorrectExp, uakeInitiator, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, hrun, rfl⟩ := hb
  suffices h : uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join by
    simpa using h
  simp only [setup, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsetup
  obtain ⟨ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, spkSigB, hspkSigB, huk, htk⟩ := hsetup
  subst huk htk
  exact run_support_initiator P hasOPK hsig hkem haead hdh msg hikA hikB hsigkB hspkB
    hspkSigB hrun

theorem uakeRecipient_perfectlyCorrect
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) := by
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact probFailure_of_liftM_PMF _
  intro b hb
  simp only [UAKE.CorrectExp, uakeRecipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, hrun, rfl⟩ := hb
  suffices h : uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join by
    simpa using h
  simp only [setup, support_map, Set.mem_image, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hsetup
  obtain ⟨x, ⟨ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, spkSigB, hspkSigB, rfl⟩,
    hswap⟩ := hsetup
  simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hswap
  obtain ⟨huk, htk⟩ := hswap
  subst huk htk
  exact run_support_recipient P hasOPK hsig hkem haead hdh msg hikA hikB hsigkB hspkB
    hspkSigB hrun

section Security

theorem uakeInitiator_secure_pq
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εkem εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : ECKey ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hkem : ∀ B : (pqkem P).IND_CCA_Adversary,
      KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_VF_Adversary P.aead,
      AEAD.INT_CTXT_VF_Advantage P.aead B ≤ εaead)
    (hencTotal : EncapsTotal P)
    (hkdfTotal : DeriveKeysTotal)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (ECKey × ECKey × ECKey × Option ECKey)
        (Key × Key × Key),
      kdfPRF.prfAdvantage D ≤ εkdf) :
    UAKE.advantage A ≤ εsig + q * (εkem + εaead + εkdf) := by
  sorry

theorem uakeInitiator_secure_dh
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εddh εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : ECKey ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hdh : AgreeComm P)
    (hagree : AgreeTotal P)
    (hddh : ∀ D : DDHAdversary, ddhDistAdvantage P D ≤ εddh)
    (haead : ∀ B : AEAD.INT_CTXT_VF_Adversary P.aead,
      AEAD.INT_CTXT_VF_Advantage P.aead B ≤ εaead)
    (hkdfTotal : DeriveKeysTotal)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (ECKey × ECKey × Option ECKey × SS)
        (Key × Key × Key),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf) :
    UAKE.advantage A ≤ εsig + q * (εddh + εaead + εkdf) := by
  sorry

end Security

end

end PQXDH.Aeneas
