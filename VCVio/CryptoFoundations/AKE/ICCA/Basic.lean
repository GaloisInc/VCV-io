/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.Basic

open OracleSpec OracleComp

namespace AKE.ICCA

variable {Msg SendK RecvK W : Type}

structure Env (proto : MTP.Scheme Msg SendK RecvK W) where
  clock : ℕ
  challenge : Option (Session proto.sender.State W)
  receivers : List (Session proto.receiver.State W)

inductive Op (W : Type) where
  | openReceiver : Op W
  | stepReceiver : ℕ → W → Op W
  | stepChallenge : W → Op W

def oracleSpec (Msg W : Type) : OracleSpec (Op W)
  | .openReceiver => ℕ × Option W
  | .stepReceiver _ _ => W ⊕ Option Msg
  | .stepChallenge _ => W ⊕ Unit

def oracleImpl (proto : MTP.Scheme Msg SendK RecvK W) (recvk : RecvK) :
    QueryImpl (oracleSpec Msg W) (StateT (Env proto) ProbComp) := fun op =>
  match op with
  | .openReceiver => do
      let (st, opening) ← (proto.receiver.init recvk : ProbComp _)
      let env ← get
      let (tr, c') := recordOpt ⟨[]⟩ opening env.clock
      let sid := env.receivers.length
      let r0 : Session proto.receiver.State W := ⟨st, tr⟩
      set { env with clock := c', receivers := env.receivers ++ [r0] }
      pure (sid, opening)
  | .stepReceiver sid w => do
      let env ← get
      match env.receivers[sid]? with
      | none => pure (.inr none)
      | some r =>
        let (st', res) ← (proto.receiver.step r.state w : ProbComp _)
        let (tr1, c1) := recordOne r.transcript w env.clock
        match res with
        | .inl (w', _) =>
            let (tr2, c2) := recordOne tr1 w' c1
            set { env with clock := c2, receivers := env.receivers.set sid ⟨st', tr2⟩ }
            pure (.inl w')
        | .inr out =>
            set { env with clock := c1, receivers := env.receivers.set sid ⟨st', tr1⟩ }
            pure (.inr out)
  | .stepChallenge w => do
      let env ← get
      match env.challenge with
      | none => pure (.inr ())
      | some c =>
        let (st', res) ← (proto.sender.step c.state w : ProbComp _)
        let (tr1, c1) := recordOne c.transcript w env.clock
        match res with
        | .inl (w', _) =>
            let (tr2, c2) := recordOne tr1 w' c1
            set { env with clock := c2, challenge := some ⟨st', tr2⟩ }
            pure (.inl w')
        | .inr out =>
            set { env with clock := c1, challenge := some ⟨st', tr1⟩ }
            pure (.inr out)

structure Adversary (proto : MTP.Scheme Msg SendK RecvK W) where
  State : Type
  choose : SendK → OracleComp (unifSpec + oracleSpec Msg W) (Msg × Msg × State)
  guess : State → Option W → OracleComp (unifSpec + oracleSpec Msg W) Bool

structure Result (proto : MTP.Scheme Msg SendK RecvK W) where
  guess : Bool
  challengeTr : Transcript W
  oracleTrs : List (Transcript W)

def chooseMessages {proto : MTP.Scheme Msg SendK RecvK W} (A : Adversary proto)
    (sendk : SendK) (recvk : RecvK) : ProbComp (Msg × Msg × (A.State × Env proto)) := do
  let init : Env proto := ⟨0, none, []⟩
  let ((m0, m1, st), env) ←
    (simulateQ (withUnif (oracleImpl proto recvk)) (A.choose sendk)).run init
  pure (m0, m1, (st, env))

def challengeSession {proto : MTP.Scheme Msg SendK RecvK W} (A : Adversary proto)
    (ch : A.State × Env proto) (sendk : SendK) (recvk : RecvK) (mb : Msg) :
    ProbComp (Result proto) := do
  let (st, env) := ch
  let (s0, opening) ← (proto.sender.init (sendk, mb) : ProbComp _)
  let (tr, c') := recordOpt ⟨[]⟩ opening env.clock
  let env' : Env proto := { env with clock := c', challenge := some ⟨s0, tr⟩ }
  let (b', env'') ← (simulateQ (withUnif (oracleImpl proto recvk)) (A.guess st opening)).run env'
  pure ⟨b', (env''.challenge.map (·.transcript)).getD ⟨[]⟩, env''.receivers.map (·.transcript)⟩

def isPingPong [DecidableEq W] {proto : MTP.Scheme Msg SendK RecvK W} (r : Result proto) : Bool :=
  pingPong (proto.rounds % 2 == 0) r.oracleTrs r.challengeTr

def Exp [DecidableEq W] {proto : MTP.Scheme Msg SendK RecvK W} (A : Adversary proto) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let (sendk, recvk) ← proto.setup
  let (m0, m1, ch) ← chooseMessages A sendk recvk
  let cr ← challengeSession A ch sendk recvk (if b then m1 else m0)
  if isPingPong cr then $ᵗ Bool
  else pure (cr.guess == b)

noncomputable def advantage [DecidableEq W] {proto : MTP.Scheme Msg SendK RecvK W}
    (A : Adversary proto) : ℝ :=
  (Pr[= true | Exp A]).toReal - 1 / 2

end AKE.ICCA
