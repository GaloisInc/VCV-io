/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Spec.Basic
import PQXDH.AKE.UAKE.Basic
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.OracleComp.QueryTracking.QueryBound

open OracleSpec OracleComp AKE

namespace PQXDH

variable {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}

inductive Message (G PQPK CT S C IdC IdK : Type) where
  | bundle : PreKeyBundle G PQPK S IdC IdK → Message G PQPK CT S C IdC IdK
  | initial : InitialMessage G CT C IdC IdK → Message G PQPK CT S C IdC IdK
  | confirmation : C → Message G PQPK CT S C IdC IdK
  deriving DecidableEq

def initiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) :
    Party (InitiatorParameters F G SS Msg K) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SS Msg K ⊕ SessionContext G PQPK Msg K ⊕ K
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
        | some ctx => do
            /- DEVIATION FROM SPEC: UAKE requires T to speak last, sending an
              authenticated message if the exchange was accepted. This prevents
              a trivial attack where the attacker simply refrains from sending
              Alice's last message, so that ping-pong is vacuously false. We
              have Bob send the final message of the exchange here in order to
              satisfy this, whereas the spec stops at Bob receiving the
              message. -/
            let conf ← P.aead.encrypt ctx.kb ctx.ad ctx.msg
            pure (.acceptAndSend (.inr ctx.sk) (.confirmation conf) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

def uakeInitiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme K (InitiatorParameters F G SS Msg K) (RecipientParameters F G SS PQPK PQSK K)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg hasOPK
  U := initiator P
  T := recipient P

def uakeRecipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme K (RecipientParameters F G SS PQPK PQSK K) (InitiatorParameters F G SS Msg K)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 4
  setup := Prod.swap <$> setup P msg hasOPK
  U := recipient P
  T := initiator P

theorem uakeInitiator_perfectlyCorrect
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hkg : P.sig.keygen = dhKeygen P.gen)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) := by
  sorry

theorem uakeRecipient_perfectlyCorrect
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hkg : P.sig.keygen = dhKeygen P.gen)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) := by
  sorry

def _root_.AKE.UAKE.Adversary.OpensAtMost {K UK TK W : Type} {proto : UAKE.Scheme K UK TK W}
    (A : UAKE.Adversary proto) (q : ℕ) : Prop :=
  (∀ uk w, (A.challenge uk w).IsQueryBoundP (· matches Sum.inr .openT) q) ∧
    (∀ st k, (A.post st k).IsQueryBoundP (· matches Sum.inr .openT) q)

def kdfRoRExp [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    (km : ProbComp (KeyMaterial G SS))
    (D : (KeyMaterial G SS → K × K × K) → K × K × K → ProbComp Bool) (b : Bool) :
    ProbComp Bool := do
  let kdf ← $ᵗ (KeyMaterial G SS → K × K × K)
  let x ← km
  let ks ← if b then pure (kdf x) else $ᵗ (K × K × K)
  D kdf ks

def KdfHidesInput [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    (km : ProbComp (KeyMaterial G SS)) (ε : ℝ) : Prop :=
  ∀ D : (KeyMaterial G SS → K × K × K) → K × K × K → ProbComp Bool,
    |(Pr[= true | kdfRoRExp km D true]).toReal -
      (Pr[= true | kdfRoRExp km D false]).toReal| ≤ ε

theorem uakeInitiator_secure_pq
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K] [SampleableType SS]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hkg : P.sig.keygen = dhKeygen P.gen)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εkem εaead εkdf : ℝ)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.advantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.IND_CTXT_Adversary P.aead,
      AEAD.IND_CTXT_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ (DH1 DH2 DH3 : G) (DH4 : Option G),
      KdfHidesInput (K := K)
        (do let ss ← $ᵗ SS; pure (DH1, DH2, DH3, DH4, ss)) εkdf) :
    UAKE.advantage A ≤ εsig + q * (εkem + εaead + εkdf) := by
  sorry

theorem uakeInitiator_secure_dh
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType (KeyMaterial G SS → K × K × K)]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hkg : P.sig.keygen = dhKeygen P.gen)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εddh εaead εkdf : ℝ)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.advantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hddh : ∀ D : DiffieHellman.DDHAdversary F G,
      DiffieHellman.ddhDistAdvantage P.gen D ≤ εddh)
    (haead : ∀ B : AEAD.IND_CTXT_Adversary P.aead,
      AEAD.IND_CTXT_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ (DH1 DH2 : G) (DH4 : Option G) (ss : SS),
      KdfHidesInput (K := K)
        (do let c ← $ᵗ F; pure (DH1, DH2, c • P.gen, DH4, ss)) εkdf) :
    UAKE.advantage A ≤ εsig + q * (εddh + εaead + εkdf) := by
  sorry

end PQXDH
