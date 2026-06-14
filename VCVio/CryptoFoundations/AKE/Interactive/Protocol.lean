/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.AsymmEncAlg.Defs
import PolyFun.Interaction.TwoParty.Strategy
import PolyFun.Interaction.TwoParty.Role
import PolyFun.Interaction.TwoParty.Decoration

/-!
# Interactive message-transmission protocols

This file models the *message transmission protocol* from DF'17
("Unilaterally-Authenticated Key Exchange", Definition 1).
-/

open OracleSpec OracleComp
open Interaction Interaction.TwoParty

universe v

/-- A message transmission protocol `Π = (Setup, S, R)` with message space
  `Msg`, sender key space `SendK`, and receiver key space `RecvK`, running in
  the effect monad `m`.

  Note that we use Spec for the protocol shape, which is more general than the
  protocol shape used in DF'17, where a protocol is linear, alternating between
  the two parties, with S speaking last. Instantiations should use the `ofRounds`
  constructor to the Spec is linear, that the parties alternate turns, and that
  S speaks last. -/
structure MsgTransmissionProtocol (m : Type → Type) [Monad m] (Msg SendK RecvK : Type) where
  /-- The shape of the message exchange: a tree whose moves are protocol messages. -/
  spec : Spec
  /-- Per-node assignment of which party sends each message (focal `S` vs counterpart). -/
  owner : RoleDecoration spec
  /-- Key generation, producing the sender and receiver keys. -/
  setup : m (SendK × RecvK)
  /-- The honest sender `S(sendk, m)` as a focal strategy with no private output. -/
  sender : SendK → Msg →
    StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec owner (fun _ => Unit)
  /-- The honest receiver `R(recvk)` as a counterpart strategy whose private
    output is a recovered message or `⊥`. -/
  receiver : RecvK →
    StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec owner
      (fun _ => Option Msg)

namespace MsgTransmissionProtocol

variable {m : Type → Type} [Monad m] {Msg SendK RecvK : Type}

/-- Run one honest session `⟨S(sendk, msg), R(recvk)⟩`, returning the session
  transcript paired with the sender's (trivial) output and the receiver's
  private output. -/
def execute (proto : MsgTransmissionProtocol m Msg SendK RecvK)
    (sendk : SendK) (recvk : RecvK) (msg : Msg) :
    m ((_tr : Spec.Transcript proto.spec) × Unit × Option Msg) :=
  Interaction.TwoParty.run proto.spec proto.owner (proto.sender sendk msg) (proto.receiver recvk)

/-- The receiver's private output `m' ∈ Msg ∪ {⊥}` after one honest session,
  i.e. the value of `⟨S(sendk, msg), R(recvk)⟩`. -/
def receiverOutput (proto : MsgTransmissionProtocol m Msg SendK RecvK)
    (sendk : SendK) (recvk : RecvK) (msg : Msg) : m (Option Msg) := do
  let ⟨_, _, out⟩ ← proto.execute sendk recvk msg
  return out

/-- Correctness experiment (Definition 1): generate keys, run one honest
  session on `msg`, and report whether the receiver recovered exactly `msg`. -/
def CorrectExp [DecidableEq Msg] (proto : MsgTransmissionProtocol m Msg SendK RecvK)
    (msg : Msg) : m Bool := do
  let (sendk, recvk) ← proto.setup
  let out ← proto.receiverOutput sendk recvk msg
  return decide (out = some msg)

/-- A protocol is perfectly correct when, for every message, an honest session
recovers it with probability `1`. -/
def PerfectlyCorrect [DecidableEq Msg]
    (proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK) : Prop :=
  ∀ msg : Msg, Pr[= true | proto.CorrectExp msg] = 1

/-- A role declaration that models property from DF'17 (page 6) that S and R
  alternate turns and that S speaks last -/
def alternatingOwner : (Ms : List Type) → RoleDecoration (Spec.ofList Ms)
  | [] => ⟨⟩
  | _ :: tl => ⟨if tl.length % 2 = 0 then Role.sender else Role.receiver,
                fun _ => alternatingOwner tl⟩

/-- Using `alternatingOwner`, above, ensures that, for an n-round protocol, R
  speaks first if n is even, and S speaks first if n is odd. -/
theorem alternatingOwner_first_role (T : Type) (tl : List Type) :
    (alternatingOwner (T :: tl)).1 = Role.receiver ↔ Even (T :: tl).length := by
  change (if tl.length % 2 = 0 then Role.sender else Role.receiver) = Role.receiver ↔ _
  rw [Nat.even_iff, List.length_cons]
  by_cases h : tl.length % 2 = 0 <;> simp [h] <;> omega

/-- Construct a `MsgTransmissionProtocol` with a linear Spec, where the parties
  alternate turns, and where S speaks last. -/
def ofRounds (Ms : List Type)
    (setup : m (SendK × RecvK))
    (sender : SendK → Msg → StrategyOver (SyntaxOver.TwoParty.pairedSpec m)
      Participant.focal (Spec.ofList Ms) (alternatingOwner Ms) (fun _ => Unit))
    (receiver : RecvK → StrategyOver (SyntaxOver.TwoParty.pairedSpec m)
      Participant.counterpart (Spec.ofList Ms) (alternatingOwner Ms) (fun _ => Option Msg)) :
    MsgTransmissionProtocol m Msg SendK RecvK where
  spec := Spec.ofList Ms
  owner := alternatingOwner Ms
  setup := setup
  sender := sender
  receiver := receiver

end MsgTransmissionProtocol

/-! ## Single-round protocols from non-interactive encryption

A non-interactive asymmetric encryption scheme is the degenerate one-round
message transmission protocol: the sender transmits a single ciphertext and the
receiver decrypts it. This exhibits the interactive framework as a genuine
generalization of the non-interactive one. -/

namespace MsgTransmissionProtocol

variable {Msg PK SK C : Type}

/-- View a non-interactive `AsymmEncAlg` as a one-round message transmission
protocol: the focal sender transmits one ciphertext, the counterpart receiver
decrypts it. The sender key is the public key and the receiver key is the secret
key. -/
def ofAsymmEncAlg (encAlg : AsymmEncAlg ProbComp Msg PK SK C) :
    MsgTransmissionProtocol ProbComp Msg PK SK :=
  ofRounds [C] encAlg.keygen
    (fun pk msg => (fun c => ⟨c, ()⟩) <$> encAlg.encrypt pk msg)
    (fun sk c => encAlg.decrypt sk c)

/-- Reduction of `run` on the one-round shape "focal sends one move, then done":
the focal party samples its move, the counterpart observes it and produces its
output. This packages the generic `run_paired_sender`/`run_paired_done`
computation rules into a single clean equation for the depth-one protocol. -/
private theorem run_oneSender {m : Type → Type} [Monad m] [LawfulMonad m] {X B : Type}
    (send : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
      (Spec.node X (fun _ => Spec.done)) (Role.sender, fun _ => PUnit.unit) (fun _ => Unit))
    (recv : StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
      (Spec.node X (fun _ => Spec.done)) (Role.sender, fun _ => PUnit.unit) (fun _ => Option B)) :
    Interaction.TwoParty.run (Spec.node X (fun _ => Spec.done))
        (Role.sender, fun _ => PUnit.unit) send recv =
      (do
        let xc ← send
        let out ← recv xc.1
        pure ⟨⟨xc.1, PUnit.unit⟩, xc.2, out⟩) := by
  have h := InteractionOver.TwoParty.run_paired_sender (m := m) (X := X)
    (rest := fun _ => Spec.done) (rRest := fun _ => PUnit.unit)
    (OutputP := fun _ => Unit) (OutputC := fun _ => Option B) send recv
  calc Interaction.TwoParty.run (Spec.node X (fun _ => Spec.done))
          (Role.sender, fun _ => PUnit.unit) send recv = _ := h
    _ = _ := by
      simp only [InteractionOver.runSpec, collectParticipantOutputs, participantProfile, pure_bind]
      rfl

/-- One honest session of the one-round protocol reduces to "encrypt then
decrypt": the receiver's recovered value is `decrypt sk (encrypt pk msg)`. -/
@[simp]
theorem ofAsymmEncAlg_receiverOutput (encAlg : AsymmEncAlg ProbComp Msg PK SK C)
    (pk : PK) (sk : SK) (msg : Msg) :
    (ofAsymmEncAlg encAlg).receiverOutput pk sk msg =
      (do let c ← encAlg.encrypt pk msg; encAlg.decrypt sk c) := by
  have hexec : (ofAsymmEncAlg encAlg).execute pk sk msg =
      (do
        let xc : (_ : C) × Unit ← (fun c => ⟨c, ()⟩) <$> encAlg.encrypt pk msg
        let out ← encAlg.decrypt sk xc.fst
        pure ⟨⟨xc.fst, PUnit.unit⟩, (xc.snd, out)⟩) :=
    run_oneSender (m := ProbComp) (X := C) (B := Msg)
      ((fun c => ⟨c, ()⟩) <$> encAlg.encrypt pk msg) (fun c => encAlg.decrypt sk c)
  simp only [receiverOutput, hexec]
  simp

/-- Key generation of the one-round protocol is the encryption scheme's key generation. -/
@[simp]
theorem ofAsymmEncAlg_setup (encAlg : AsymmEncAlg ProbComp Msg PK SK C) :
    (ofAsymmEncAlg encAlg).setup = encAlg.keygen := rfl

/-- The correctness experiment of the one-round protocol built from an encryption
scheme is exactly the scheme's own correctness experiment. This is the
correctness half of "for 1-round protocols, iCCA security is IND-CCA security". -/
@[simp]
theorem ofAsymmEncAlg_correctExp [DecidableEq Msg]
    (encAlg : AsymmEncAlg ProbComp Msg PK SK C) (msg : Msg) :
    (ofAsymmEncAlg encAlg).CorrectExp msg = encAlg.CorrectExp msg := by
  simp only [CorrectExp, AsymmEncAlg.CorrectExp, ofAsymmEncAlg_setup,
    ofAsymmEncAlg_receiverOutput, bind_assoc]

end MsgTransmissionProtocol
