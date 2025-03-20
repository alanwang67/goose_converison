From Perennial.program_proof.session Require Export session_prelude definitions coq_session.

Definition Ev : Z := 0.
Definition Wfr : Z := 1.
Definition Mw : Z := 2.
Definition Mr : Z := 3.
Definition Ryw : Z := 4.
Definition Ca : Z := 5.

Module CoqSessionClient.

  Definition coq_read (c: Client.t) (serverId: u64) : Message.t :=
    match uint.Z c.(Client.SessionSemantic) with
    | 0 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 1 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 2 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 3 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 4 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (c.(Client.WriteVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | _ => Message.mk 0 (c.(Client.Id)) serverId 0 0 (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    end.

  Definition coq_write (c: Client.t) (serverId: u64) (value: u64) : Message.t :=
    match uint.Z c.(Client.SessionSemantic) with
    | 0 => Message.mk 0 (c.(Client.Id)) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 1 => Message.mk 0 (c.(Client.Id)) serverId 1 value (c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 2 => Message.mk 0 (c.(Client.Id)) serverId 1 value (c.(Client.WriteVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0                    
    | 3 => Message.mk 0 (c.(Client.Id)) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 4 => Message.mk 0 (c.(Client.Id)) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | _ => Message.mk 0 (c.(Client.Id)) serverId 1 value (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    end.

  Definition coq_processRequest (c: Client.t) (requestType serverId value: u64) (ackMessage: Message.t) : (Client.t * Message.t) :=
    match (uint.Z requestType) with
    | 0 => (c, coq_read c serverId)
    | 1 => (c, coq_write c serverId value)
    | _ =>
        if ((uint.Z ackMessage.(Message.MessageType)) =? 4) then 
          match (uint.Z ackMessage.(Message.S2C_Client_OperationType)) with
          | 0 => (Client.mk c.(Client.Id) c.(Client.NumberOfServers) c.(Client.WriteVersionVector) ackMessage.(Message.S2C_Client_VersionVector) c.(Client.SessionSemantic), Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
          | _ => (Client.mk c.(Client.Id) c.(Client.NumberOfServers) (ackMessage.(Message.S2C_Client_VersionVector)) c.(Client.ReadVersionVector) c.(Client.SessionSemantic), Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
          end
        else
          (c, Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
    end.

End CoqSessionClient.

Export CoqSessionClient.
