(* autogenerated from command-line-arguments *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

Definition Operation := struct.decl [
  "VersionVector" :: slice.T uint64T;
  "Data" :: uint64T
].

Definition Message := struct.decl [
  "MessageType" :: uint64T;
  "C2S_Client_Id" :: uint64T;
  "C2S_Server_Id" :: uint64T;
  "C2S_Client_OperationType" :: uint64T;
  "C2S_Client_Data" :: uint64T;
  "C2S_Client_VersionVector" :: slice.T uint64T;
  "S2S_Gossip_Sending_ServerId" :: uint64T;
  "S2S_Gossip_Receiving_ServerId" :: uint64T;
  "S2S_Gossip_Operations" :: slice.T (struct.t Operation);
  "S2S_Gossip_Index" :: uint64T;
  "S2S_Acknowledge_Gossip_Sending_ServerId" :: uint64T;
  "S2S_Acknowledge_Gossip_Receiving_ServerId" :: uint64T;
  "S2S_Acknowledge_Gossip_Index" :: uint64T;
  "S2C_Client_OperationType" :: uint64T;
  "S2C_Client_Data" :: uint64T;
  "S2C_Client_VersionVector" :: slice.T uint64T;
  "S2C_Server_Id" :: uint64T;
  "S2C_Client_Number" :: uint64T
].

Definition Server := struct.decl [
  "Id" :: uint64T;
  "NumberOfServers" :: uint64T;
  "UnsatisfiedRequests" :: slice.T (struct.t Message);
  "VectorClock" :: slice.T uint64T;
  "OperationsPerformed" :: slice.T (struct.t Operation);
  "MyOperations" :: slice.T (struct.t Operation);
  "PendingOperations" :: slice.T (struct.t Operation);
  "GossipAcknowledgements" :: slice.T uint64T
].

Definition compareVersionVector: val :=
  rec: "compareVersionVector" "v1" "v2" :=
    let: "output" := ref_to boolT #true in
    let: "i" := ref_to uint64T #0 in
    let: "l" := ref_to uint64T (slice.len "v1") in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "l")); (λ: <>, Skip) := λ: <>,
      (if: (SliceGet uint64T "v1" (![uint64T] "i")) < (SliceGet uint64T "v2" (![uint64T] "i"))
      then
        "output" <-[boolT] #false;;
        Break
      else
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue));;
    ![boolT] "output".

Definition lexicographicCompare: val :=
  rec: "lexicographicCompare" "v1" "v2" :=
    let: "output" := ref_to boolT #false in
    let: "i" := ref_to uint64T #0 in
    let: "l" := ref_to uint64T (slice.len "v1") in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "l")); (λ: <>, Skip) := λ: <>,
      (if: (SliceGet uint64T "v1" (![uint64T] "i")) = (SliceGet uint64T "v2" (![uint64T] "i"))
      then
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue
      else
        "output" <-[boolT] ((SliceGet uint64T "v1" (![uint64T] "i")) > (SliceGet uint64T "v2" (![uint64T] "i")));;
        Break));;
    ![boolT] "output".

Definition maxTwoInts: val :=
  rec: "maxTwoInts" "x" "y" :=
    (if: "x" > "y"
    then "x"
    else "y").

Definition maxTS: val :=
  rec: "maxTS" "t1" "t2" :=
    let: "i" := ref_to uint64T #0 in
    let: "length" := ref_to uint64T (slice.len "t1") in
    let: "output" := ref_to (slice.T uint64T) (NewSlice uint64T (slice.len "t1")) in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "length")); (λ: <>, Skip) := λ: <>,
      SliceSet uint64T (![slice.T uint64T] "output") (![uint64T] "i") (maxTwoInts (SliceGet uint64T "t1" (![uint64T] "i")) (SliceGet uint64T "t2" (![uint64T] "i")));;
      "i" <-[uint64T] ((![uint64T] "i") + #1);;
      Continue);;
    ![slice.T uint64T] "output".

Definition oneOffVersionVector: val :=
  rec: "oneOffVersionVector" "v1" "v2" :=
    let: "output" := ref_to boolT #true in
    let: "canApply" := ref_to boolT #true in
    let: "i" := ref_to uint64T #0 in
    let: "l" := ref_to uint64T (slice.len "v1") in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "l")); (λ: <>, Skip) := λ: <>,
      (if: (![boolT] "canApply") && (((SliceGet uint64T "v1" (![uint64T] "i")) + #1) = (SliceGet uint64T "v2" (![uint64T] "i")))
      then
        "canApply" <-[boolT] #false;;
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue
      else
        (if: (SliceGet uint64T "v1" (![uint64T] "i")) < (SliceGet uint64T "v2" (![uint64T] "i"))
        then "output" <-[boolT] #false
        else #());;
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue));;
    (![boolT] "output") && (~ (![boolT] "canApply")).

Definition equalSlices: val :=
  rec: "equalSlices" "s1" "s2" :=
    let: "output" := ref_to boolT #true in
    let: "i" := ref_to uint64T #0 in
    let: "l" := ref_to uint64T (slice.len "s1") in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "l")); (λ: <>, Skip) := λ: <>,
      (if: (SliceGet uint64T "s1" (![uint64T] "i")) ≠ (SliceGet uint64T "s2" (![uint64T] "i"))
      then
        "output" <-[boolT] #false;;
        Break
      else
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue));;
    ![boolT] "output".

Definition equalOperations: val :=
  rec: "equalOperations" "o1" "o2" :=
    (equalSlices (struct.get Operation "VersionVector" "o1") (struct.get Operation "VersionVector" "o2")) && ((struct.get Operation "Data" "o1") = (struct.get Operation "Data" "o2")).

Definition binarySearch: val :=
  rec: "binarySearch" "s" "needle" :=
    let: "i" := ref_to uint64T #0 in
    let: "j" := ref_to uint64T (slice.len "s") in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "j")); (λ: <>, Skip) := λ: <>,
      let: "mid" := (![uint64T] "i") + (((![uint64T] "j") - (![uint64T] "i")) `quot` #2) in
      (if: lexicographicCompare (struct.get Operation "VersionVector" "needle") (struct.get Operation "VersionVector" (SliceGet (struct.t Operation) "s" "mid"))
      then
        "i" <-[uint64T] ("mid" + #1);;
        Continue
      else
        "j" <-[uint64T] "mid";;
        Continue));;
    ![uint64T] "i".

Definition sortedInsert: val :=
  rec: "sortedInsert" "s" "value" :=
    let: "index" := binarySearch "s" "value" in
    (if: (slice.len "s") = "index"
    then SliceAppend (struct.t Operation) "s" "value"
    else
      let: "right" := SliceAppendSlice (struct.t Operation) (SliceSingleton "value") (SliceSkip (struct.t Operation) "s" "index") in
      let: "result" := SliceAppendSlice (struct.t Operation) (SliceTake "s" "index") "right" in
      "result").

Definition mergeOperations: val :=
  rec: "mergeOperations" "l1" "l2" :=
    (if: ((slice.len "l1") = #0) && ((slice.len "l2") = #0)
    then NewSlice (struct.t Operation) #0
    else
      let: "output" := ref_to (slice.T (struct.t Operation)) (SliceAppendSlice (struct.t Operation) (NewSlice (struct.t Operation) #0) "l1") in
      let: "i" := ref_to uint64T #0 in
      let: "l" := ref_to uint64T (slice.len "l2") in
      Skip;;
      (for: (λ: <>, (![uint64T] "i") < (![uint64T] "l")); (λ: <>, Skip) := λ: <>,
        "output" <-[slice.T (struct.t Operation)] (sortedInsert (![slice.T (struct.t Operation)] "output") (SliceGet (struct.t Operation) "l2" (![uint64T] "i")));;
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue);;
      let: "prev" := ref_to uint64T #1 in
      let: "curr" := ref_to uint64T #1 in
      Skip;;
      (for: (λ: <>, (![uint64T] "curr") < (slice.len (![slice.T (struct.t Operation)] "output"))); (λ: <>, Skip) := λ: <>,
        (if: (~ (equalOperations (SliceGet (struct.t Operation) (![slice.T (struct.t Operation)] "output") ((![uint64T] "curr") - #1)) (SliceGet (struct.t Operation) (![slice.T (struct.t Operation)] "output") (![uint64T] "curr"))))
        then
          SliceSet (struct.t Operation) (![slice.T (struct.t Operation)] "output") (![uint64T] "prev") (SliceGet (struct.t Operation) (![slice.T (struct.t Operation)] "output") (![uint64T] "curr"));;
          "prev" <-[uint64T] ((![uint64T] "prev") + #1)
        else #());;
        "curr" <-[uint64T] ((![uint64T] "curr") + #1);;
        Continue);;
      SliceTake (![slice.T (struct.t Operation)] "output") (![uint64T] "prev")).

Definition deleteAtIndexOperation: val :=
  rec: "deleteAtIndexOperation" "l" "index" :=
    let: "ret" := ref_to (slice.T (struct.t Operation)) (NewSlice (struct.t Operation) #0) in
    "ret" <-[slice.T (struct.t Operation)] (SliceAppendSlice (struct.t Operation) (![slice.T (struct.t Operation)] "ret") (SliceTake "l" "index"));;
    SliceAppendSlice (struct.t Operation) (![slice.T (struct.t Operation)] "ret") (SliceSkip (struct.t Operation) "l" ("index" + #1)).

Definition deleteAtIndexMessage: val :=
  rec: "deleteAtIndexMessage" "l" "index" :=
    let: "ret" := ref_to (slice.T (struct.t Message)) (NewSlice (struct.t Message) #0) in
    "ret" <-[slice.T (struct.t Message)] (SliceAppendSlice (struct.t Message) (![slice.T (struct.t Message)] "ret") (SliceTake "l" "index"));;
    SliceAppendSlice (struct.t Message) (![slice.T (struct.t Message)] "ret") (SliceSkip (struct.t Message) "l" ("index" + #1)).

Definition getDataFromOperationLog: val :=
  rec: "getDataFromOperationLog" "l" :=
    (if: (slice.len "l") > #0
    then struct.get Operation "Data" (SliceGet (struct.t Operation) "l" ((slice.len "l") - #1))
    else #0).

Definition receiveGossip: val :=
  rec: "receiveGossip" "server" "request" :=
    (if: (slice.len (struct.get Message "S2S_Gossip_Operations" "request")) = #0
    then "server"
    else
      let: "s" := ref_to (struct.t Server) "server" in
      struct.storeF Server "PendingOperations" "s" (mergeOperations (struct.get Server "PendingOperations" (![struct.t Server] "s")) (struct.get Message "S2S_Gossip_Operations" "request"));;
      let: "i" := ref_to uint64T #0 in
      Skip;;
      (for: (λ: <>, (![uint64T] "i") < (slice.len (struct.get Server "PendingOperations" (![struct.t Server] "s")))); (λ: <>, Skip) := λ: <>,
        (if: oneOffVersionVector (struct.get Server "VectorClock" (![struct.t Server] "s")) (struct.get Operation "VersionVector" (SliceGet (struct.t Operation) (struct.get Server "PendingOperations" (![struct.t Server] "s")) (![uint64T] "i")))
        then
          struct.storeF Server "OperationsPerformed" "s" (mergeOperations (struct.get Server "OperationsPerformed" (![struct.t Server] "s")) (SliceSingleton (SliceGet (struct.t Operation) (struct.get Server "PendingOperations" (![struct.t Server] "s")) (![uint64T] "i"))));;
          struct.storeF Server "VectorClock" "s" (maxTS (struct.get Server "VectorClock" (![struct.t Server] "s")) (struct.get Operation "VersionVector" (SliceGet (struct.t Operation) (struct.get Server "PendingOperations" (![struct.t Server] "s")) (![uint64T] "i"))));;
          struct.storeF Server "PendingOperations" "s" (deleteAtIndexOperation (struct.get Server "PendingOperations" (![struct.t Server] "s")) (![uint64T] "i"));;
          Continue
        else
          "i" <-[uint64T] ((![uint64T] "i") + #1);;
          Continue));;
      ![struct.t Server] "s").

Definition acknowledgeGossip: val :=
  rec: "acknowledgeGossip" "server" "request" :=
    (if: (struct.get Message "S2S_Acknowledge_Gossip_Sending_ServerId" "request") ≥ (slice.len (struct.get Server "GossipAcknowledgements" "server"))
    then "server"
    else
      SliceSet uint64T (struct.get Server "GossipAcknowledgements" "server") (struct.get Message "S2S_Acknowledge_Gossip_Sending_ServerId" "request") (maxTwoInts (SliceGet uint64T (struct.get Server "GossipAcknowledgements" "server") (struct.get Message "S2S_Acknowledge_Gossip_Sending_ServerId" "request")) (struct.get Message "S2S_Acknowledge_Gossip_Index" "request"));;
      "server").

Definition getGossipOperations: val :=
  rec: "getGossipOperations" "server" "serverId" :=
    let: "ret" := ref_to (slice.T (struct.t Operation)) (NewSlice (struct.t Operation) #0) in
    (if: ("serverId" ≥ (slice.len (struct.get Server "GossipAcknowledgements" "server"))) || ((SliceGet uint64T (struct.get Server "GossipAcknowledgements" "server") "serverId") ≥ (slice.len (struct.get Server "MyOperations" "server")))
    then ![slice.T (struct.t Operation)] "ret"
    else SliceAppendSlice (struct.t Operation) (![slice.T (struct.t Operation)] "ret") (SliceSkip (struct.t Operation) (struct.get Server "MyOperations" "server") (SliceGet uint64T (struct.get Server "GossipAcknowledgements" "server") "serverId"))).

Definition processClientRequest: val :=
  rec: "processClientRequest" "server" "request" :=
    let: "reply" := ref_to (struct.t Message) (struct.mk Message [
    ]) in
    (if: (~ (compareVersionVector (struct.get Server "VectorClock" "server") (struct.get Message "C2S_Client_VersionVector" "request")))
    then (#false, "server", ![struct.t Message] "reply")
    else
      (if: (struct.get Message "C2S_Client_OperationType" "request") = #0
      then
        struct.storeF Message "MessageType" "reply" #4;;
        struct.storeF Message "S2C_Client_OperationType" "reply" #0;;
        struct.storeF Message "S2C_Client_Data" "reply" (getDataFromOperationLog (struct.get Server "OperationsPerformed" "server"));;
        struct.storeF Message "S2C_Client_VersionVector" "reply" (SliceAppendSlice uint64T (NewSlice uint64T #0) (struct.get Server "VectorClock" "server"));;
        struct.storeF Message "S2C_Server_Id" "reply" (struct.get Server "Id" "server");;
        struct.storeF Message "S2C_Client_Number" "reply" (struct.get Message "C2S_Client_Id" "request");;
        (#true, "server", ![struct.t Message] "reply")
      else
        let: "s" := ref_to (struct.t Server) "server" in
        SliceSet uint64T (struct.get Server "VectorClock" (![struct.t Server] "s")) (struct.get Server "Id" "server") ((SliceGet uint64T (struct.get Server "VectorClock" (![struct.t Server] "s")) (struct.get Server "Id" "server")) + #1);;
        struct.storeF Server "OperationsPerformed" "s" (sortedInsert (struct.get Server "OperationsPerformed" (![struct.t Server] "s")) (struct.mk Operation [
          "VersionVector" ::= SliceAppendSlice uint64T (NewSlice uint64T #0) (struct.get Server "VectorClock" "server");
          "Data" ::= struct.get Message "C2S_Client_Data" "request"
        ]));;
        struct.storeF Server "MyOperations" "s" (sortedInsert (struct.get Server "MyOperations" (![struct.t Server] "s")) (struct.mk Operation [
          "VersionVector" ::= SliceAppendSlice uint64T slice.nil (struct.get Server "VectorClock" (![struct.t Server] "s"));
          "Data" ::= struct.get Message "C2S_Client_Data" "request"
        ]));;
        struct.storeF Message "MessageType" "reply" #4;;
        struct.storeF Message "S2C_Client_OperationType" "reply" #1;;
        struct.storeF Message "S2C_Client_Data" "reply" #0;;
        struct.storeF Message "S2C_Client_VersionVector" "reply" (SliceAppendSlice uint64T (NewSlice uint64T #0) (struct.get Server "VectorClock" "server"));;
        struct.storeF Message "S2C_Server_Id" "reply" (struct.get Server "Id" "server");;
        struct.storeF Message "S2C_Client_Number" "reply" (struct.get Message "C2S_Client_Id" "request");;
        (#true, ![struct.t Server] "s", ![struct.t Message] "reply"))).

Definition processRequest: val :=
  rec: "processRequest" "server" "request" :=
    let: "outGoingRequests" := ref_to (slice.T (struct.t Message)) (NewSlice (struct.t Message) #0) in
    let: "s" := ref_to (struct.t Server) "server" in
    (if: (struct.get Message "MessageType" "request") = #0
    then
      let: "succeeded" := ref_to boolT #false in
      let: "reply" := ref_to (struct.t Message) (struct.mk Message [
      ]) in
      let: (("0_ret", "1_ret"), "2_ret") := processClientRequest (![struct.t Server] "s") "request" in
      "succeeded" <-[boolT] "0_ret";;
      "s" <-[struct.t Server] "1_ret";;
      "reply" <-[struct.t Message] "2_ret";;
      (if: ![boolT] "succeeded"
      then "outGoingRequests" <-[slice.T (struct.t Message)] (SliceAppend (struct.t Message) (![slice.T (struct.t Message)] "outGoingRequests") (![struct.t Message] "reply"))
      else struct.storeF Server "UnsatisfiedRequests" "s" (SliceAppend (struct.t Message) (struct.get Server "UnsatisfiedRequests" (![struct.t Server] "s")) "request"))
    else
      (if: (struct.get Message "MessageType" "request") = #1
      then
        "s" <-[struct.t Server] (receiveGossip (![struct.t Server] "s") "request");;
        "outGoingRequests" <-[slice.T (struct.t Message)] (SliceAppend (struct.t Message) (![slice.T (struct.t Message)] "outGoingRequests") (struct.mk Message [
          "MessageType" ::= #2;
          "S2S_Acknowledge_Gossip_Sending_ServerId" ::= struct.get Server "Id" (![struct.t Server] "s");
          "S2S_Acknowledge_Gossip_Receiving_ServerId" ::= struct.get Message "S2S_Gossip_Sending_ServerId" "request";
          "S2S_Acknowledge_Gossip_Index" ::= struct.get Message "S2S_Gossip_Index" "request"
        ]));;
        let: "i" := ref_to uint64T #0 in
        let: "reply" := ref_to (struct.t Message) (struct.mk Message [
        ]) in
        let: "succeeded" := ref_to boolT #false in
        Skip;;
        (for: (λ: <>, (![uint64T] "i") < (slice.len (struct.get Server "UnsatisfiedRequests" (![struct.t Server] "s")))); (λ: <>, Skip) := λ: <>,
          let: (("0_ret", "1_ret"), "2_ret") := processClientRequest (![struct.t Server] "s") (SliceGet (struct.t Message) (struct.get Server "UnsatisfiedRequests" (![struct.t Server] "s")) (![uint64T] "i")) in
          "succeeded" <-[boolT] "0_ret";;
          "s" <-[struct.t Server] "1_ret";;
          "reply" <-[struct.t Message] "2_ret";;
          (if: ![boolT] "succeeded"
          then
            "outGoingRequests" <-[slice.T (struct.t Message)] (SliceAppend (struct.t Message) (![slice.T (struct.t Message)] "outGoingRequests") (![struct.t Message] "reply"));;
            struct.storeF Server "UnsatisfiedRequests" "s" (deleteAtIndexMessage (struct.get Server "UnsatisfiedRequests" (![struct.t Server] "s")) (![uint64T] "i"));;
            Continue
          else
            "i" <-[uint64T] ((![uint64T] "i") + #1);;
            Continue))
      else
        (if: (struct.get Message "MessageType" "request") = #2
        then "s" <-[struct.t Server] (acknowledgeGossip (![struct.t Server] "s") "request")
        else
          (if: (struct.get Message "MessageType" "request") = #3
          then
            let: "i" := ref_to uint64T #0 in
            Skip;;
            (for: (λ: <>, (![uint64T] "i") < (struct.get Server "NumberOfServers" "server")); (λ: <>, Skip) := λ: <>,
              (if: (![uint64T] "i") ≠ (struct.get Server "Id" (![struct.t Server] "s"))
              then
                let: "index" := ![uint64T] "i" in
                let: "operations" := getGossipOperations (![struct.t Server] "s") "index" in
                (if: (slice.len "operations") ≠ #0
                then
                  "outGoingRequests" <-[slice.T (struct.t Message)] (SliceAppend (struct.t Message) (![slice.T (struct.t Message)] "outGoingRequests") (struct.mk Message [
                    "MessageType" ::= #1;
                    "S2S_Gossip_Sending_ServerId" ::= struct.get Server "Id" (![struct.t Server] "s");
                    "S2S_Gossip_Receiving_ServerId" ::= "index";
                    "S2S_Gossip_Operations" ::= "operations";
                    "S2S_Gossip_Index" ::= (slice.len (struct.get Server "MyOperations" (![struct.t Server] "s"))) - #1
                  ]))
                else #())
              else #());;
              "i" <-[uint64T] ((![uint64T] "i") + #1);;
              Continue)
          else #()))));;
    (![struct.t Server] "s", ![slice.T (struct.t Message)] "outGoingRequests").

End code.
