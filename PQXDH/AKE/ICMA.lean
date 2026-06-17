/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.AKE.Basic

open OracleSpec OracleComp

namespace AKE.ICMA

variable {Msg SendK RecvK W : Type}

structure Env (proto : MTP.Scheme Msg SendK RecvK W) where
  clock : ℕ
  challenge : Session proto.receiver.State W
  challengeOutput : Option (Option Msg)
  senders : List (Session proto.sender.State W)

inductive Op (Msg W : Type) where
  | openSender : Msg → Op Msg W
  | stepSender : ℕ → W → Op Msg W
  | stepChallenge : W → Op Msg W

def oracleSpec (Msg W : Type) : OracleSpec (Op Msg W)
  | .openSender _ => ℕ × Option W
  | .stepSender _ _ => W ⊕ Unit
  | .stepChallenge _ => W ⊕ Option Msg

def oracleImpl (proto : MTP.Scheme Msg SendK RecvK W) (sendk : SendK) :
    QueryImpl (oracleSpec Msg W) (StateT (Env proto) ProbComp) := fun op =>
  match op with
  | .openSender m => do
      let (st, opening) ← (proto.sender.init (sendk, m) : ProbComp _)
      let env ← get
      let (tr, c') := recordOpt ⟨[]⟩ opening env.clock
      let sid := env.senders.length
      let s0 : Session proto.sender.State W := ⟨st, tr⟩
      set { env with clock := c', senders := env.senders ++ [s0] }
      pure (sid, opening)
  | .stepSender sid w => do
      let env ← get
      match env.senders[sid]? with
      | none => pure (.inr ())
      | some s =>
        let (st', res) ← (proto.sender.step s.state w : ProbComp _)
        let (tr1, c1) := recordOne s.transcript w env.clock
        match res with
        | .inl (w', _) =>
            let (tr2, c2) := recordOne tr1 w' c1
            set { env with clock := c2, senders := env.senders.set sid ⟨st', tr2⟩ }
            pure (.inl w')
        | .inr out =>
            set { env with clock := c1, senders := env.senders.set sid ⟨st', tr1⟩ }
            pure (.inr out)
  | .stepChallenge w => do
      let env ← get
      match env.challengeOutput with
      | some m => pure (.inr m)
      | none => do
          let (st', res) ← (proto.receiver.step env.challenge.state w : ProbComp _)
          let (tr1, c1) := recordOne env.challenge.transcript w env.clock
          match res with
          | .inl (w', _) =>
              let (tr2, c2) := recordOne tr1 w' c1
              set { env with clock := c2, challenge := ⟨st', tr2⟩ }
              pure (.inl w')
          | .inr out =>
              set { env with clock := c1, challenge := ⟨st', tr1⟩, challengeOutput := some out }
              pure (.inr out)

structure Adversary (proto : MTP.Scheme Msg SendK RecvK W) where
  run : RecvK → OracleComp (unifSpec + oracleSpec Msg W) Unit

structure Result (proto : MTP.Scheme Msg SendK RecvK W) where
  mstar : Option Msg
  challengeTr : Transcript W
  oracleTrs : List (Transcript W)

def challengeSession {proto : MTP.Scheme Msg SendK RecvK W} (A : Adversary proto)
    (sendk : SendK) (recvk : RecvK) : ProbComp (Result proto) := do
  let (r0, _) ← (proto.receiver.init recvk : ProbComp _)
  let init : Env proto := ⟨0, ⟨r0, ⟨[]⟩⟩, none, []⟩
  let (_, env) ← (simulateQ (withUnif (oracleImpl proto sendk)) (A.run recvk)).run init
  pure ⟨env.challengeOutput.join, env.challenge.transcript, env.senders.map (·.transcript)⟩

def isPingPong [DecidableEq W] {proto : MTP.Scheme Msg SendK RecvK W} (r : Result proto) : Bool :=
  pingPong (proto.rounds % 2 == 1) r.oracleTrs r.challengeTr

def Exp [DecidableEq W] {proto : MTP.Scheme Msg SendK RecvK W} (A : Adversary proto) :
    ProbComp Bool := do
  let (sendk, recvk) ← proto.setup
  let r ← challengeSession A sendk recvk
  if r.mstar.isSome && !isPingPong r then return true
  else return false

noncomputable def advantage [DecidableEq W] {proto : MTP.Scheme Msg SendK RecvK W}
    (A : Adversary proto) : ℝ :=
  (Pr[= true | Exp A]).toReal

end AKE.ICMA
