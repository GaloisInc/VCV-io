/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.AEAD
import PQXDH.AKE.UAKE.Basic
import VCVio.CryptoFoundations.KeyEncapMech
import VCVio.CryptoFoundations.SignatureAlg

open OracleSpec OracleComp AKE

namespace PQXDH

variable {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}

def EncodeEC {G PQPK : Type} (pk : G) : G ⊕ PQPK := Sum.inl pk

def EncodeKEM {G PQPK : Type} (pk : PQPK) : G ⊕ PQPK := Sum.inr pk

abbrev KeyMaterial (G SS : Type) : Type := G × G × G × Option G × SS

structure Parameters (F G SS PQPK PQSK CT S C Msg K IdC IdK : Type) where
  gen : G
  pqkem : KEMScheme ProbComp SS PQPK PQSK CT
  sig : SignatureAlg ProbComp (G ⊕ PQPK) G F S
  aead : AEAD.Scheme ProbComp Msg K (G × G × PQPK) C
  idEC : G → IdC
  idKEM : PQPK → IdK

def dhKeygen [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (gen : G) : ProbComp (G × F) := do
  let sk ← $ᵗ F
  return (sk • gen, sk)

def DH [Field F] [AddCommGroup G] [Module F G] (sk : F) (pk : G) : G := sk • pk

structure InitiatorParameters (F G SS Msg K : Type) where
  ikA : G × F
  msg : Msg
  kdf : KeyMaterial G SS → K

structure RecipientParameters (F G SS PQPK PQSK K : Type) where
  ikB : G × F
  spkB : G × F
  opkB : Option (G × F)
  pqpkB : PQPK × PQSK
  kdf : KeyMaterial G SS → K

structure PreKeyBundle (G PQPK S IdC IdK : Type) where
  ikB : G
  spkB : G × IdC
  spkSig : S
  pqpkB : PQPK × IdK
  pqpkSig : S
  opkB : Option (G × IdC)

structure InitialMessage (G CT C IdC IdK : Type) where
  ikA : G
  ekA : G
  ct : CT
  idSPK : IdC
  idPQPK : IdK
  idOPK : Option IdC
  ctxt : C

def setup [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K)]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    ProbComp (InitiatorParameters F G SS Msg K × RecipientParameters F G SS PQPK PQSK K) := do
  let kdf ← $ᵗ (KeyMaterial G SS → K)
  let ikA ← dhKeygen P.gen
  let ikB ← dhKeygen P.gen
  let spkB ← dhKeygen P.gen
  let opkB ← if hasOPK then some <$> dhKeygen P.gen else pure none
  let pqpkB ← P.pqkem.keygen
  return ({ ikA := ikA, msg := msg, kdf := kdf },
    { ikB := ikB, spkB := spkB, opkB := opkB, pqpkB := pqpkB, kdf := kdf })

def publish (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK)
    (p : RecipientParameters F G SS PQPK PQSK K) :
    ProbComp (PreKeyBundle G PQPK S IdC IdK) := do
  let spkSig ← P.sig.sign p.ikB.1 p.ikB.2 (EncodeEC p.spkB.1)
  let pqpkSig ← P.sig.sign p.ikB.1 p.ikB.2 (EncodeKEM p.pqpkB.1)
  return { ikB := p.ikB.1
           spkB := (p.spkB.1, P.idEC p.spkB.1)
           spkSig := spkSig
           pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
           pqpkSig := pqpkSig
           opkB := p.opkB.map fun opk => (opk.1, P.idEC opk.1) }

def initiate [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK)
    (p : InitiatorParameters F G SS Msg K)
    (bundle : PreKeyBundle G PQPK S IdC IdK) :
    ProbComp (Option (InitialMessage G CT C IdC IdK × K)) := do
  let okSPK ← P.sig.verify bundle.ikB (EncodeEC bundle.spkB.1) bundle.spkSig
  let okPQPK ← P.sig.verify bundle.ikB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSig
  if !(okSPK && okPQPK) then return none
  let ekA : G × F ← dhKeygen P.gen
  let (CT, SS) ← P.pqkem.encaps bundle.pqpkB.1
  let DH1 := DH p.ikA.2 bundle.spkB.1
  let DH2 := DH ekA.2 bundle.ikB
  let DH3 := DH ekA.2 bundle.spkB.1
  let DH4 := bundle.opkB.map fun opk => DH ekA.2 opk.1
  let SK := p.kdf (DH1, DH2, DH3, DH4, SS)
  let AD := (p.ikA.1, bundle.ikB, bundle.pqpkB.1)
  let ctxt ← P.aead.encrypt SK AD p.msg
  return some ({ ikA := p.ikA.1
                 ekA := ekA.1
                 ct := CT
                 idSPK := bundle.spkB.2
                 idPQPK := bundle.pqpkB.2
                 idOPK := bundle.opkB.map Prod.snd
                 ctxt := ctxt }, SK)

def accept [Field F] [AddCommGroup G] [Module F G] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK)
    (p : RecipientParameters F G SS PQPK PQSK K)
    (msg : InitialMessage G CT C IdC IdK) :
    ProbComp (Option (K × Msg)) := do
  if msg.idSPK ≠ P.idEC p.spkB.1 ∨ msg.idPQPK ≠ P.idKEM p.pqpkB.1 ∨
      msg.idOPK ≠ p.opkB.map (fun opk => P.idEC opk.1) then return none
  let some SS ← P.pqkem.decaps p.pqpkB.2 msg.ct | return none
  let DH1 := DH p.spkB.2 msg.ikA
  let DH2 := DH p.ikB.2 msg.ekA
  let DH3 := DH p.spkB.2 msg.ekA
  let DH4 := p.opkB.map fun opk => DH opk.2 msg.ekA
  let SK := p.kdf (DH1, DH2, DH3, DH4, SS)
  let AD := (msg.ikA, p.ikB.1, p.pqpkB.1)
  match P.aead.decrypt SK AD msg.ctxt with
  | some m => return some (SK, m)
  | none => return none

inductive Message (G PQPK CT S C IdC IdK : Type) where
  | bundle : PreKeyBundle G PQPK S IdC IdK → Message G PQPK CT S C IdC IdK
  | initial : InitialMessage G CT C IdC IdK → Message G PQPK CT S C IdC IdK

def initiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) :
    Party (InitiatorParameters F G SS Msg K) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SS Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiate P p b with
        | some (im, SK) => pure (.acceptAndSend (.inr SK) (.initial im) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

def recipient [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) :
    Party (RecipientParameters F G SS PQPK PQSK K) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := RecipientParameters F G SS PQPK PQSK K ⊕ K
  init := fun p => do
    let bundle ← publish P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← accept P p im with
        | some (SK, _) => pure (.complete (.inr SK))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

def uakeInitiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K)] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme K (InitiatorParameters F G SS Msg K) (RecipientParameters F G SS PQPK PQSK K)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 1
  setup := setup P msg hasOPK
  U := initiator P
  T := recipient P

def uakeRecipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K)] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme K (RecipientParameters F G SS PQPK PQSK K) (InitiatorParameters F G SS Msg K)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 2
  setup := Prod.swap <$> setup P msg hasOPK
  U := recipient P
  T := initiator P

end PQXDH
