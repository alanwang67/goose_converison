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

Definition Client := struct.decl [
  "Id" :: uint64T;
  "NumberOfServers" :: uint64T;
  "WriteVersionVector" :: slice.T uint64T;
  "ReadVersionVector" :: slice.T uint64T;
  "SessionSemantic" :: uint64T
].

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

Definition read: val :=
  rec: "read" "client" "serverId" :=
    let: "reply" := ref_to (struct.t Message) (struct.mk Message [
    ]) in
    (if: (((struct.get Client "SessionSemantic" "client") = #0) || ((struct.get Client "SessionSemantic" "client") = #1)) || ((struct.get Client "SessionSemantic" "client") = #2)
    then
      struct.storeF Message "MessageType" "reply" #0;;
      struct.storeF Message "C2S_Client_Id" "reply" (struct.get Client "Id" "client");;
      struct.storeF Message "C2S_Client_OperationType" "reply" #0;;
      struct.storeF Message "C2S_Client_Data" "reply" #0;;
      struct.storeF Message "C2S_Server_Id" "reply" "serverId";;
      struct.storeF Message "C2S_Client_VersionVector" "reply" (NewSlice uint64T (struct.get Client "NumberOfServers" "client"))
    else
      (if: (struct.get Client "SessionSemantic" "client") = #3
      then
        struct.storeF Message "MessageType" "reply" #0;;
        struct.storeF Message "C2S_Client_Id" "reply" (struct.get Client "Id" "client");;
        struct.storeF Message "C2S_Client_OperationType" "reply" #0;;
        struct.storeF Message "C2S_Client_Data" "reply" #0;;
        struct.storeF Message "C2S_Server_Id" "reply" "serverId";;
        struct.storeF Message "C2S_Client_VersionVector" "reply" (SliceAppendSlice uint64T (NewSlice uint64T #0) (struct.get Client "ReadVersionVector" "client"))
      else
        (if: (struct.get Client "SessionSemantic" "client") = #4
        then
          struct.storeF Message "MessageType" "reply" #0;;
          struct.storeF Message "C2S_Client_Id" "reply" (struct.get Client "Id" "client");;
          struct.storeF Message "C2S_Client_OperationType" "reply" #0;;
          struct.storeF Message "C2S_Client_Data" "reply" #0;;
          struct.storeF Message "C2S_Server_Id" "reply" "serverId";;
          struct.storeF Message "C2S_Client_VersionVector" "reply" (SliceAppendSlice uint64T (NewSlice uint64T #0) (struct.get Client "WriteVersionVector" "client"))
        else
          (if: (struct.get Client "SessionSemantic" "client") = #5
          then
            struct.storeF Message "MessageType" "reply" #0;;
            struct.storeF Message "C2S_Client_Id" "reply" (struct.get Client "Id" "client");;
            struct.storeF Message "C2S_Client_OperationType" "reply" #0;;
            struct.storeF Message "C2S_Client_Data" "reply" #0;;
            struct.storeF Message "C2S_Server_Id" "reply" "serverId";;
            struct.storeF Message "C2S_Client_VersionVector" "reply" (maxTS (struct.get Client "WriteVersionVector" "client") (struct.get Client "ReadVersionVector" "client"))
          else #()))));;
    ![struct.t Message] "reply".

Definition write: val :=
  rec: "write" "client" "serverId" "value" :=
    let: "reply" := ref_to (struct.t Message) (struct.mk Message [
    ]) in
    (if: (((struct.get Client "SessionSemantic" "client") = #0) || ((struct.get Client "SessionSemantic" "client") = #3)) || ((struct.get Client "SessionSemantic" "client") = #4)
    then
      struct.storeF Message "MessageType" "reply" #0;;
      struct.storeF Message "C2S_Client_Id" "reply" (struct.get Client "Id" "client");;
      struct.storeF Message "C2S_Client_OperationType" "reply" #1;;
      struct.storeF Message "C2S_Client_Data" "reply" "value";;
      struct.storeF Message "C2S_Server_Id" "reply" "serverId";;
      struct.storeF Message "C2S_Client_VersionVector" "reply" (NewSlice uint64T (struct.get Client "NumberOfServers" "client"))
    else
      (if: (struct.get Client "SessionSemantic" "client") = #1
      then
        struct.storeF Message "MessageType" "reply" #0;;
        struct.storeF Message "C2S_Client_Id" "reply" (struct.get Client "Id" "client");;
        struct.storeF Message "C2S_Client_OperationType" "reply" #1;;
        struct.storeF Message "C2S_Client_Data" "reply" "value";;
        struct.storeF Message "C2S_Server_Id" "reply" "serverId";;
        struct.storeF Message "C2S_Client_VersionVector" "reply" (SliceAppendSlice uint64T (NewSlice uint64T #0) (struct.get Client "ReadVersionVector" "client"))
      else
        (if: (struct.get Client "SessionSemantic" "client") = #2
        then
          struct.storeF Message "MessageType" "reply" #0;;
          struct.storeF Message "C2S_Client_Id" "reply" (struct.get Client "Id" "client");;
          struct.storeF Message "C2S_Client_OperationType" "reply" #1;;
          struct.storeF Message "C2S_Client_Data" "reply" "value";;
          struct.storeF Message "C2S_Server_Id" "reply" "serverId";;
          struct.storeF Message "C2S_Client_VersionVector" "reply" (SliceAppendSlice uint64T (NewSlice uint64T #0) (struct.get Client "WriteVersionVector" "client"))
        else
          (if: (struct.get Client "SessionSemantic" "client") = #5
          then
            struct.storeF Message "MessageType" "reply" #0;;
            struct.storeF Message "C2S_Client_Id" "reply" (struct.get Client "Id" "client");;
            struct.storeF Message "C2S_Client_OperationType" "reply" #1;;
            struct.storeF Message "C2S_Client_Data" "reply" "value";;
            struct.storeF Message "C2S_Server_Id" "reply" "serverId";;
            struct.storeF Message "C2S_Client_VersionVector" "reply" (maxTS (struct.get Client "WriteVersionVector" "client") (struct.get Client "ReadVersionVector" "client"))
          else #()))));;
    ![struct.t Message] "reply".

Definition processRequest: val :=
  rec: "processRequest" "client" "requestType" "serverId" "value" "ackMessage" :=
    let: "msg" := ref_to (struct.t Message) (struct.mk Message [
    ]) in
    (if: "requestType" = #0
    then "msg" <-[struct.t Message] (read "client" "serverId")
    else
      (if: "requestType" = #1
      then "msg" <-[struct.t Message] (write "client" "serverId" "value")
      else
        (if: "requestType" = #2
        then
          (if: (struct.get Message "S2C_Client_OperationType" "ackMessage") = #0
          then struct.storeF Client "ReadVersionVector" "client" (SliceAppendSlice uint64T (NewSlice uint64T #0) (struct.get Message "S2C_Client_VersionVector" "ackMessage"))
          else #());;
          (if: (struct.get Message "S2C_Client_OperationType" "ackMessage") = #1
          then struct.storeF Client "WriteVersionVector" "client" (SliceAppendSlice uint64T (NewSlice uint64T #0) (struct.get Message "S2C_Client_VersionVector" "ackMessage"))
          else #())
        else #())));;
    ("client", ![struct.t Message] "msg").

End code.
