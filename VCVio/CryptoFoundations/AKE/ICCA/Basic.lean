/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.Game

open OracleSpec OracleComp Interaction Interaction.TwoParty
open TimestampedTranscript MsgTransmissionProtocol AKE

namespace ICCA

variable {Msg SendK RecvK : Type}

def Roracle (proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK) :
    OracleSpec (SenderStrategy ProbComp proto.Ms) :=
  fun _ => TimestampedTranscript proto.Ms × Option Msg

def roracleImpl {proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK} (recvk : RecvK) :
    QueryImpl (Roracle proto) (StateT (Env proto) ProbComp) := fun sendStrat => do
  let ⟨tr, _, out⟩ ←
    (Interaction.TwoParty.run proto.spec proto.owner sendStrat (proto.receiver recvk) : ProbComp _)
  let session ← logSession tr
  pure (session, out)

def oracleImpl {proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK} (recvk : RecvK) :
    QueryImpl (unifSpec + Roracle proto) (StateT (Env proto) ProbComp) :=
  withUnif (roracleImpl (proto := proto) recvk)

structure Adversary (proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK) where
  State : Type
  choose : SendK → OracleComp (unifSpec + Roracle proto) (Msg × Msg × CptStrategy proto × State)
  guess : State → Spec.Transcript proto.spec → OracleComp (unifSpec + Roracle proto) Bool

variable {proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK}
  [DecidableEq (Spec.Transcript (Spec.ofList proto.Ms))]

def isPingPong (cr : ChallengeResult proto Bool) : Bool :=
  pingPong Role.sender cr.oracleSessions cr.transcript

def chooseMessages (A : Adversary proto) (sendk : SendK) (recvk : RecvK) :
    ProbComp (Msg × Msg × (CptStrategy proto × A.State × Env proto)) := do
  let ((m0, m1, cpt, st), env) ← (simulateQ (oracleImpl recvk) (A.choose sendk)).run ⟨0, []⟩
  pure (m0, m1, (cpt, st, env))

def challengeSession (A : Adversary proto) (recvk : RecvK)
    (ch : CptStrategy proto × A.State × Env proto) (sendk : SendK) (mb : Msg) :
    ProbComp (ChallengeResult proto Bool) := do
  let (cpt, st, env) := ch
  let ⟨tr, _, _⟩ ← Interaction.TwoParty.run proto.spec proto.owner (proto.sender sendk mb) cpt
  let challengeTr := stampAt proto tr env.clock
  let (b', env') ←
    (simulateQ (oracleImpl recvk) (A.guess st tr)).run
      ⟨env.clock + proto.Ms.length, env.sessions⟩
  pure ⟨b', challengeTr, env'.sessions⟩

def Exp (A : Adversary proto) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (sendk, recvk) ← proto.setup
  let (m0, m1, ch) ← chooseMessages A sendk recvk
  let cr ← challengeSession A recvk ch sendk (if b then m1 else m0)
  if isPingPong cr then $ᵗ Bool
  else pure (cr.outcome == b)

noncomputable def advantage (A : Adversary proto) : ℝ :=
  (Pr[= true | Exp A]).toReal - 1 / 2

end ICCA
