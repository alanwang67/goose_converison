From Perennial.program_proof.session Require Export session_prelude.

Module Operation.

  Lemma struct_ty_operation_unfold :
    struct.t Operation = (slice.T uint64T * (uint64T * unitT))%ht.
  Proof. reflexivity. Qed.

  Record t :=
    mk {
        VersionVector: list u64 ;
        Data:          u64 ;
      }.

End Operation.

Module Message.

  Record t := mk {
                  MessageType: u64 ;

                  C2S_Client_Id:            u64;
	          C2S_Server_Id:            u64;
	          C2S_Client_OperationType: u64;
	          C2S_Client_Data:          u64;
	          C2S_Client_VersionVector: list u64;

	          S2S_Gossip_Sending_ServerId:   u64;
	          S2S_Gossip_Receiving_ServerId: u64;
	          S2S_Gossip_Operations:         list Operation.t;
	          S2S_Gossip_Index:              u64;

	          S2S_Acknowledge_Gossip_Sending_ServerId:   u64;
	          S2S_Acknowledge_Gossip_Receiving_ServerId: u64;
	          S2S_Acknowledge_Gossip_Index:              u64;

	          S2C_Client_OperationType: u64;    
	          S2C_Client_Data:          u64;
	          S2C_Client_VersionVector: list u64;
                  S2C_Server_Id:            u64;
	          S2C_Client_Number:        u64;
                }.

End Message.

Module Server.

  Record t :=
    mk {
        Id:                     u64 ;
	NumberOfServers:        u64 ;
	UnsatisfiedRequests:    list Message.t ;
	VectorClock:            list u64 ;
	OperationsPerformed:    list Operation.t ;
	MyOperations:           list Operation.t ;
	PendingOperations:      list Operation.t ;
	GossipAcknowledgements: list u64 ;
      }.

End Server.

Module Client.

  Record t :=
    mk {
        Id: u64 ;
        NumberOfServers: u64 ;
        WriteVersionVector: list u64 ;
        ReadVersionVector: list u64 ;
        SessionSemantic: u64 ;
      }.
  
End Client.
       

Section heap.
  Context `{hG: !heapGS Σ}.

  Definition operation_val (op:Slice.t*u64) : val :=
    (slice_val op.1, (#op.2, #()))%V.

  Theorem operation_val_t op : val_ty (operation_val op) (struct.t Operation).
  Proof.
    repeat constructor; auto.
  Qed.

  Hint Resolve operation_val_t : core.

  Global Instance operation_into_val : IntoVal (Slice.t*u64).
  Proof.
    refine {| into_val.to_val := operation_val;
             from_val := λ v, match v with
                              | (slice_v, (#(LitInt d), #()))%V =>
                                  match from_val slice_v with
                                  | Some s => Some (s, d)
                                  | None => None
                                  end
                              | _ => None
                              end;
             IntoVal_def := (IntoVal_def Slice.t, W64 0);
           |}.
    destruct v as [[a []] d]; done. 
  Defined.

  #[global] Instance operation_into_val_for_type : IntoValForType (Slice.t*u64) (struct.t Operation).
  Proof. constructor; auto. Qed.

  Definition is_operation (opv: Slice.t*u64) (op: Operation.t) (len_opv: nat) : iProp Σ :=
    ⌜opv.2 = op.(Operation.Data)⌝ ∗
    ⌜len_opv = length (op.(Operation.VersionVector))⌝ ∗
    own_slice_small opv.1 uint64T DfracDiscarded op.(Operation.VersionVector).

  Definition operation_slice' (op_s: Slice.t) (op: list Operation.t) (n: nat) (dq: dfrac) : iProp Σ :=
    ∃ ops, own_slice op_s (struct.t Operation) dq ops ∗
           [∗ list] opv;o ∈ ops;op, is_operation opv o n.

  Definition operation_slice (s: Slice.t) (l: list Operation.t) (n: nat) : iProp Σ :=
    operation_slice' s l n (DfracOwn 1).

  Definition message_val (msg:u64*u64*u64*u64*u64*Slice.t*u64*u64*Slice.t*u64*u64*u64*u64*u64*u64*Slice.t*u64*u64) : val :=
    (#msg.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1,
       (#msg.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
          (#msg.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
             (#msg.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
                (#msg.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
                   (slice_val msg.1.1.1.1.1.1.1.1.1.1.1.1.2,
                      (#msg.1.1.1.1.1.1.1.1.1.1.1.2,
                         (#msg.1.1.1.1.1.1.1.1.1.1.2,
                            (slice_val msg.1.1.1.1.1.1.1.1.1.2,
                               (#msg.1.1.1.1.1.1.1.1.2,
                                  (#msg.1.1.1.1.1.1.1.2,
                                     (#msg.1.1.1.1.1.1.2,
                                        (#msg.1.1.1.1.1.2,
                                           (#msg.1.1.1.1.2,
                                              (#msg.1.1.1.2,
                                                 (slice_val msg.1.1.2,
                                                    (#msg.1.2,
                                                       (#msg.2,
                                                          #()))))))))))))))))))%V.

  Lemma redefine_message_val
    : message_val = @SessionPrelude.value_of (tuple_of[u64,u64,u64,u64,u64,Slice.t,u64,u64,Slice.t,u64,u64,u64,u64,u64,u64,Slice.t,u64,u64]) _.
  Proof.
    reflexivity.
  Defined.

  Theorem message_val_t msg : val_ty (message_val msg) (struct.t server.Message).
  Proof.
    repeat constructor; auto.
  Qed.

  Hint Resolve message_val_t : core.

  Definition message_from_val (v : val) : option (u64*u64*u64*u64*u64*Slice.t*u64*u64*Slice.t*u64*u64*u64*u64*u64*u64*Slice.t*u64*u64) :=
    match v with
    | (#(LitInt MessageType),
         (#(LitInt C2S_Client_Id),
            (#(LitInt C2S_Server_Id),
               (#(LitInt C2S_Client_OperationType),
                  (#(LitInt C2S_Client_Data),
                     (C2S_Client_VersionVector,
                        (#(LitInt S2S_Gossip_Sending_ServerId),
                           (#(LitInt S2S_Gossip_Receiving_ServerId),
                              (S2S_Gossip_Operations,
                                 (#(LitInt S2S_Gossip_Index),
                                    (#(LitInt S2S_Acknowledge_Gossip_Sending_ServerId),
                                       (#(LitInt S2S_Acknowledge_Gossip_Receiving_ServerId),
                                          (#(LitInt S2S_Acknowledge_Gossip_Index),
                                             (#(LitInt S2C_Client_OperationType),
                                                (#(LitInt S2C_Client_Data),
                                                   (S2C_Client_VersionVector,
                                                      (#(LitInt S2C_Server_Id),
                                                         (#(LitInt S2C_Client_Number), #()))))))))))))))))))%V =>
        match ((from_val C2S_Client_VersionVector: option Slice.t),
                 (from_val S2S_Gossip_Operations: option Slice.t),
                   (from_val S2C_Client_VersionVector: option Slice.t)) with
        | (Some s1, Some s2, Some s3) => Some (MessageType,
                                                 C2S_Client_Id,
                                                   C2S_Server_Id,
                                                     C2S_Client_OperationType,
                                                       C2S_Client_Data,
                                                         s1, 
                                                           S2S_Gossip_Sending_ServerId,
                                                             S2S_Gossip_Receiving_ServerId, s2, S2S_Gossip_Index,
                                                               S2S_Acknowledge_Gossip_Sending_ServerId,
                                                                 S2S_Acknowledge_Gossip_Receiving_ServerId,
                                                                   S2S_Acknowledge_Gossip_Index,
                                                                     S2C_Client_OperationType,
                                                                       S2C_Client_Data,
                                                                         s3,
                                                                           S2C_Server_Id,
                                                                             S2C_Client_Number)
        | _ => None
        end
    | _ => None
    end.
  
  Global Instance message_into_val : IntoVal (u64*u64*u64*u64*u64*Slice.t*u64*u64*Slice.t*u64*u64*u64*u64*u64*u64*Slice.t*u64*u64).
  Proof.
    refine {| into_val.to_val := message_val;
             from_val := message_from_val ;
             IntoVal_def := (W64 0, W64 0, W64 0, W64 0, W64 0,
                               IntoVal_def Slice.t, W64 0, W64 0,
                                 IntoVal_def Slice.t,
                                   W64 0, W64 0, W64 0, W64 0, W64 0,
                                     W64 0, IntoVal_def Slice.t,
                                       W64 0, W64 0);
           |}.
    destruct v. repeat destruct p. simpl. f_equal.
    destruct t1. destruct t0. destruct t.
    simpl. auto.
  Defined. 

  #[global] Instance message_into_val_for_type : IntoValForType (u64*u64*u64*u64*u64*Slice.t*u64*u64*Slice.t*u64*u64*u64*u64*u64*u64*Slice.t*u64*u64) (struct.t server.Message).
  Proof. constructor; auto. simpl. repeat split; auto. Qed.

  Definition is_message (msgv: tuple_of[u64,u64,u64,u64,u64,Slice.t,u64,u64,Slice.t,u64,u64,u64,u64,u64,u64,Slice.t,u64,u64])
    (msg: Message.t) (n: nat) (len_c2s: nat) (len_s2c: nat) : iProp Σ :=
    ⌜msgv!(0) = msg.(Message.MessageType)⌝ ∗
    ⌜msgv!(1) = msg.(Message.C2S_Client_Id)⌝ ∗
    ⌜msgv!(2) = msg.(Message.C2S_Server_Id)⌝ ∗
    ⌜msgv!(3) = msg.(Message.C2S_Client_OperationType)⌝ ∗
    ⌜msgv!(4) = msg.(Message.C2S_Client_Data)⌝ ∗
    own_slice_small msgv!(5) uint64T (DfracOwn 1) msg.(Message.C2S_Client_VersionVector) ∗
    ⌜len_c2s = length msg.(Message.C2S_Client_VersionVector)⌝ ∗
    ⌜msgv!(6) = msg.(Message.S2S_Gossip_Sending_ServerId)⌝ ∗
    ⌜msgv!(7) = msg.(Message.S2S_Gossip_Receiving_ServerId)⌝ ∗
    operation_slice msgv!(8) msg.(Message.S2S_Gossip_Operations) n ∗
    ⌜msgv!(9) = msg.(Message.S2S_Gossip_Index)⌝ ∗
    ⌜msgv!(10) = msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId)⌝ ∗
    ⌜msgv!(11) = msg.(Message.S2S_Acknowledge_Gossip_Receiving_ServerId)⌝ ∗
    ⌜msgv!(12) = msg.(Message.S2S_Acknowledge_Gossip_Index)⌝ ∗
    ⌜msgv!(13) = msg.(Message.S2C_Client_OperationType)⌝ ∗
    ⌜msgv!(14) = msg.(Message.S2C_Client_Data)⌝ ∗
    own_slice_small msgv!(15) uint64T (DfracOwn 1) msg.(Message.S2C_Client_VersionVector) ∗
    ⌜len_s2c = length msg.(Message.S2C_Client_VersionVector)⌝ ∗
    ⌜msgv!(16) = msg.(Message.S2C_Server_Id)⌝ ∗
    ⌜msgv!(17) = msg.(Message.S2C_Client_Number)⌝.

  Definition message_slice (s: Slice.t) (l: list Message.t) (n: nat) : iProp Σ :=
    ∃ msgs, own_slice s (struct.t server.Message) (DfracOwn 1) msgs ∗
            [∗ list] mv;m ∈ msgs;l, ∃ len_c2s, ∃ len_s2c, is_message mv m n len_c2s len_s2c.

  Definition server_val (s: u64*u64*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t) : val :=
    (#s.1.1.1.1.1.1.1,
       (#s.1.1.1.1.1.1.2,
          (slice_val s.1.1.1.1.1.2,
             (slice_val s.1.1.1.1.2,
                (slice_val s.1.1.1.2,
                   (slice_val s.1.1.2,
                      (slice_val s.1.2,
                         (slice_val s.2,
                            #()))))))))%V.

  Lemma redefine_server_val
    : server_val = @SessionPrelude.value_of (tuple_of [u64,u64,Slice.t,Slice.t,Slice.t,Slice.t,Slice.t,Slice.t]) _.
  Proof.
    reflexivity.
  Defined.

  Theorem server_val_t msg : val_ty (server_val msg) (struct.t server.Server).
  Proof.
    repeat constructor; auto.
  Qed.

  Hint Resolve server_val_t : core.

  Definition server_from_val (v : val) : option (u64*u64*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t) :=
    match v with
    | (#(LitInt Id),
         (#(LitInt NumberOfServers),
            (UnsatisfiedRequests,
               (VectorClock,
                  (OperationsPerformed,
                     (MyOperations,
                        (PendingOperations,
                           (GossipAcknowledgements, #()))))))))%V =>
        match ((from_val UnsatisfiedRequests: option Slice.t),
                 (from_val VectorClock: option Slice.t),
                   (from_val OperationsPerformed: option Slice.t),
                     (from_val MyOperations: option Slice.t),
                       (from_val PendingOperations: option Slice.t),
                         (from_val GossipAcknowledgements: option Slice.t)
              ) with
        | (Some s1, Some s2, Some s3, Some s4, Some s5, Some s6) =>
            Some (Id, NumberOfServers, s1, s2, s3, s4, s5, s6)
        | _ => None
        end
    | _ => None
    end.
  
  Global Instance server_into_val : IntoVal (u64*u64*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t).
  Proof.
    refine {| into_val.to_val := server_val;
             from_val := server_from_val ;
             IntoVal_def := (W64 0, W64 0, 
                               IntoVal_def Slice.t,
                                 IntoVal_def Slice.t,
                                   IntoVal_def Slice.t,
                                     IntoVal_def Slice.t,
                                       IntoVal_def Slice.t,
                                         IntoVal_def Slice.t);
           |}.
    destruct v. repeat destruct p. simpl. f_equal.
    destruct t0. destruct t. destruct t1. destruct t2. destruct t3.
    destruct t4. 
    simpl. auto.
  Defined.

  #[global] Instance server_into_val_for_type : IntoValForType (u64*u64*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t) (struct.t server.Server).
  Proof. constructor; auto. simpl. repeat split; auto. Qed.

  Definition is_server (sv: tuple_of [u64,u64,Slice.t,Slice.t,Slice.t,Slice.t,Slice.t,Slice.t]) (s: Server.t)
    (n: nat) (len_vc: nat) (len_op: nat) (len_mo: nat) (len_po: nat) (len_ga: nat) (OWN_UnsatisfiedRequests: bool) : iProp Σ :=
    ⌜sv!(0) = s.(Server.Id)⌝ ∗
    ⌜sv!(1) = s.(Server.NumberOfServers)⌝ ∗
    (if OWN_UnsatisfiedRequests then message_slice sv!(2) s.(Server.UnsatisfiedRequests) n else emp)%I ∗
    own_slice_small sv!(3) uint64T (DfracOwn 1) s.(Server.VectorClock) ∗
    ⌜len_vc = length s.(Server.VectorClock)⌝ ∗
    operation_slice sv!(4) s.(Server.OperationsPerformed) len_op ∗
    operation_slice sv!(5) s.(Server.MyOperations) len_mo ∗
    operation_slice sv!(6) s.(Server.PendingOperations) len_po ∗
    own_slice_small sv!(7) uint64T (DfracOwn 1) s.(Server.GossipAcknowledgements) ∗
    ⌜len_ga = length s.(Server.GossipAcknowledgements)⌝.

End heap.
