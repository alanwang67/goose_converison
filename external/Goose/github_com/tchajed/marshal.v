(* autogenerated from github.com/tchajed/marshal *)
From Perennial.new_goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.
From Goose Require github_com.tchajed.goose.machine.

Section code.
Context `{ffi_syntax}.
Local Coercion Var' s: expr := Var s.

(* marshal.go *)

Definition Enc := [
  "b" :: sliceT byteT;
  "off" :: ptrT
].

Definition NewEncFromSlice : val :=
  rec: "NewEncFromSlice" "b" :=
    exception_do (let: "b" := ref_ty (sliceT byteT) "b" in
    return: (struct.make Enc [
       "b" ::= ![sliceT byteT] "b";
       "off" ::= ref_ty uint64T (zero_val uint64T)
     ]);;;
    do:  #()).

Definition NewEnc : val :=
  rec: "NewEnc" "sz" :=
    exception_do (let: "sz" := ref_ty uint64T "sz" in
    let: "b" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := slice.make2 byteT (![uint64T] "sz") in
    do:  "b" <-[sliceT byteT] "$a0";;;
    return: (NewEncFromSlice (![sliceT byteT] "b"));;;
    do:  #()).

Definition Enc__PutInt : val :=
  rec: "Enc__PutInt" "enc" "x" :=
    exception_do (let: "x" := ref_ty uint64T "x" in
    let: "enc" := ref_ty (structT Enc) "enc" in
    let: "off" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc")) in
    do:  "off" <-[uint64T] "$a0";;;
    do:  machine.UInt64Put (SliceSkip byteT (![sliceT byteT] (struct.field_ref Enc "b" "enc")) (![uint64T] "off")) (![uint64T] "x");;;
    do:  (![ptrT] (struct.field_ref Enc "off" "enc")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc"))) + #8);;;
    do:  #()).

Definition Enc__PutInt32 : val :=
  rec: "Enc__PutInt32" "enc" "x" :=
    exception_do (let: "x" := ref_ty uint32T "x" in
    let: "enc" := ref_ty (structT Enc) "enc" in
    let: "off" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc")) in
    do:  "off" <-[uint64T] "$a0";;;
    do:  machine.UInt32Put (SliceSkip byteT (![sliceT byteT] (struct.field_ref Enc "b" "enc")) (![uint64T] "off")) (![uint32T] "x");;;
    do:  (![ptrT] (struct.field_ref Enc "off" "enc")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc"))) + #4);;;
    do:  #()).

Definition Enc__PutInts : val :=
  rec: "Enc__PutInts" "enc" "xs" :=
    exception_do (let: "xs" := ref_ty (sliceT uint64T) "xs" in
    let: "enc" := ref_ty (structT Enc) "enc" in
    do:  let: "$range" := ![sliceT uint64T] "xs" in
    slice.for_range uint64T "$range" (λ: <> "x",
      let: "x" := ref_ty uint64T "x" in
      do:  (Enc__PutInt (![structT Enc] "enc")) (![uint64T] "x");;;
      do:  #());;;
    do:  #()).

Definition Enc__PutBytes : val :=
  rec: "Enc__PutBytes" "enc" "b" :=
    exception_do (let: "b" := ref_ty (sliceT byteT) "b" in
    let: "enc" := ref_ty (structT Enc) "enc" in
    let: "off" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc")) in
    do:  "off" <-[uint64T] "$a0";;;
    let: "n" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := SliceCopy byteT (SliceSkip byteT (![sliceT byteT] (struct.field_ref Enc "b" "enc")) (![uint64T] "off")) (![sliceT byteT] "b") in
    do:  "n" <-[uint64T] "$a0";;;
    do:  (![ptrT] (struct.field_ref Enc "off" "enc")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc"))) + (![uint64T] "n"));;;
    do:  #()).

Definition bool2byte : val :=
  rec: "bool2byte" "b" :=
    exception_do (let: "b" := ref_ty boolT "b" in
    (if: ![boolT] "b"
    then
      return: (#(U8 1));;;
      do:  #()
    else
      return: (#(U8 0));;;
      do:  #());;;
    do:  #()).

Definition Enc__PutBool : val :=
  rec: "Enc__PutBool" "enc" "b" :=
    exception_do (let: "b" := ref_ty boolT "b" in
    let: "enc" := ref_ty (structT Enc) "enc" in
    let: "off" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc")) in
    do:  "off" <-[uint64T] "$a0";;;
    let: "$a0" := bool2byte (![boolT] "b") in
    do:  (slice.elem_ref byteT (![sliceT byteT] (struct.field_ref Enc "b" "enc")) (![uint64T] "off")) <-[byteT] "$a0";;;
    do:  (![ptrT] (struct.field_ref Enc "off" "enc")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Enc "off" "enc"))) + #1);;;
    do:  #()).

Definition Enc__Finish : val :=
  rec: "Enc__Finish" "enc" :=
    exception_do (let: "enc" := ref_ty (structT Enc) "enc" in
    return: (![sliceT byteT] (struct.field_ref Enc "b" "enc"));;;
    do:  #()).

Definition Dec := [
  "b" :: sliceT byteT;
  "off" :: ptrT
].

Definition NewDec : val :=
  rec: "NewDec" "b" :=
    exception_do (let: "b" := ref_ty (sliceT byteT) "b" in
    return: (struct.make Dec [
       "b" ::= ![sliceT byteT] "b";
       "off" ::= ref_ty uint64T (zero_val uint64T)
     ]);;;
    do:  #()).

Definition Dec__GetInt : val :=
  rec: "Dec__GetInt" "dec" :=
    exception_do (let: "dec" := ref_ty (structT Dec) "dec" in
    let: "off" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec")) in
    do:  "off" <-[uint64T] "$a0";;;
    do:  (![ptrT] (struct.field_ref Dec "off" "dec")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec"))) + #8);;;
    return: (machine.UInt64Get (SliceSkip byteT (![sliceT byteT] (struct.field_ref Dec "b" "dec")) (![uint64T] "off")));;;
    do:  #()).

Definition Dec__GetInt32 : val :=
  rec: "Dec__GetInt32" "dec" :=
    exception_do (let: "dec" := ref_ty (structT Dec) "dec" in
    let: "off" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec")) in
    do:  "off" <-[uint64T] "$a0";;;
    do:  (![ptrT] (struct.field_ref Dec "off" "dec")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec"))) + #4);;;
    return: (machine.UInt32Get (SliceSkip byteT (![sliceT byteT] (struct.field_ref Dec "b" "dec")) (![uint64T] "off")));;;
    do:  #()).

Definition Dec__GetInts : val :=
  rec: "Dec__GetInts" "dec" "num" :=
    exception_do (let: "num" := ref_ty uint64T "num" in
    let: "dec" := ref_ty (structT Dec) "dec" in
    let: "xs" := ref_ty (sliceT uint64T) (zero_val (sliceT uint64T)) in
    (let: "i" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := #0 in
    do:  "i" <-[uint64T] "$a0";;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "num")); (λ: <>, do:  "i" <-[uint64T] ((![uint64T] "i") + #1);;;
    #()) := λ: <>,
      let: "$a0" := slice.append uint64T (![sliceT uint64T] "xs") (slice.literal uint64T [(Dec__GetInt (![structT Dec] "dec")) #()]) in
      do:  "xs" <-[sliceT uint64T] "$a0";;;
      do:  #()));;;
    return: (![sliceT uint64T] "xs");;;
    do:  #()).

Definition Dec__GetBytes : val :=
  rec: "Dec__GetBytes" "dec" "num" :=
    exception_do (let: "num" := ref_ty uint64T "num" in
    let: "dec" := ref_ty (structT Dec) "dec" in
    let: "off" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec")) in
    do:  "off" <-[uint64T] "$a0";;;
    let: "b" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := SliceSubslice byteT (![sliceT byteT] (struct.field_ref Dec "b" "dec")) (![uint64T] "off") ((![uint64T] "off") + (![uint64T] "num")) in
    do:  "b" <-[sliceT byteT] "$a0";;;
    do:  (![ptrT] (struct.field_ref Dec "off" "dec")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec"))) + (![uint64T] "num"));;;
    return: (![sliceT byteT] "b");;;
    do:  #()).

Definition Dec__GetBool : val :=
  rec: "Dec__GetBool" "dec" :=
    exception_do (let: "dec" := ref_ty (structT Dec) "dec" in
    let: "off" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec")) in
    do:  "off" <-[uint64T] "$a0";;;
    do:  (![ptrT] (struct.field_ref Dec "off" "dec")) <-[uint64T] ((![uint64T] (![ptrT] (struct.field_ref Dec "off" "dec"))) + #1);;;
    (if: (![byteT] (slice.elem_ref byteT (![sliceT byteT] (struct.field_ref Dec "b" "dec")) (![uint64T] "off"))) = #(U8 0)
    then
      return: (#false);;;
      do:  #()
    else
      return: (#true);;;
      do:  #());;;
    do:  #()).

(* stateless.go *)

Definition compute_new_cap : val :=
  rec: "compute_new_cap" "old_cap" "min_cap" :=
    exception_do (let: "min_cap" := ref_ty uint64T "min_cap" in
    let: "old_cap" := ref_ty uint64T "old_cap" in
    let: "new_cap" := ref_ty uint64T ((![uint64T] "old_cap") * #2) in
    (if: (![uint64T] "new_cap") < (![uint64T] "min_cap")
    then
      let: "$a0" := ![uint64T] "min_cap" in
      do:  "new_cap" <-[uint64T] "$a0";;;
      do:  #()
    else do:  #());;;
    return: (![uint64T] "new_cap");;;
    do:  #()).

(* Grow a slice to have at least `additional` unused bytes in the capacity.
   Runtime-check against overflow. *)
Definition reserve : val :=
  rec: "reserve" "b" "additional" :=
    exception_do (let: "additional" := ref_ty uint64T "additional" in
    let: "b" := ref_ty (sliceT byteT) "b" in
    let: "min_cap" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := std.SumAssumeNoOverflow (slice.len (![sliceT byteT] "b")) (![uint64T] "additional") in
    do:  "min_cap" <-[uint64T] "$a0";;;
    (if: (slice.cap (![sliceT byteT] "b")) < (![uint64T] "min_cap")
    then
      let: "new_cap" := ref_ty uint64T (zero_val uint64T) in
      let: "$a0" := compute_new_cap (slice.cap (![sliceT byteT] "b")) (![uint64T] "min_cap") in
      do:  "new_cap" <-[uint64T] "$a0";;;
      let: "dest" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
      let: "$a0" := slice.make3 byteT (slice.len (![sliceT byteT] "b")) (![uint64T] "new_cap") in
      do:  "dest" <-[sliceT byteT] "$a0";;;
      do:  SliceCopy byteT (![sliceT byteT] "dest") (![sliceT byteT] "b");;;
      return: (![sliceT byteT] "dest");;;
      do:  #()
    else
      return: (![sliceT byteT] "b");;;
      do:  #());;;
    do:  #()).

Definition ReadInt : val :=
  rec: "ReadInt" "b" :=
    exception_do (let: "b" := ref_ty (sliceT byteT) "b" in
    let: "i" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := machine.UInt64Get (![sliceT byteT] "b") in
    do:  "i" <-[uint64T] "$a0";;;
    return: (![uint64T] "i", SliceSkip byteT (![sliceT byteT] "b") #8);;;
    do:  #()).

Definition ReadInt32 : val :=
  rec: "ReadInt32" "b" :=
    exception_do (let: "b" := ref_ty (sliceT byteT) "b" in
    let: "i" := ref_ty uint32T (zero_val uint32T) in
    let: "$a0" := machine.UInt32Get (![sliceT byteT] "b") in
    do:  "i" <-[uint32T] "$a0";;;
    return: (![uint32T] "i", SliceSkip byteT (![sliceT byteT] "b") #4);;;
    do:  #()).

(* ReadBytes reads `l` bytes from b and returns (bs, rest) *)
Definition ReadBytes : val :=
  rec: "ReadBytes" "b" "l" :=
    exception_do (let: "l" := ref_ty uint64T "l" in
    let: "b" := ref_ty (sliceT byteT) "b" in
    let: "s" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := SliceTake (![sliceT byteT] "b") (![uint64T] "l") in
    do:  "s" <-[sliceT byteT] "$a0";;;
    return: (![sliceT byteT] "s", SliceSkip byteT (![sliceT byteT] "b") (![uint64T] "l"));;;
    do:  #()).

(* Like ReadBytes, but avoids keeping the source slice [b] alive. *)
Definition ReadBytesCopy : val :=
  rec: "ReadBytesCopy" "b" "l" :=
    exception_do (let: "l" := ref_ty uint64T "l" in
    let: "b" := ref_ty (sliceT byteT) "b" in
    let: "s" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := slice.make2 byteT (![uint64T] "l") in
    do:  "s" <-[sliceT byteT] "$a0";;;
    do:  SliceCopy byteT (![sliceT byteT] "s") (SliceTake (![sliceT byteT] "b") (![uint64T] "l"));;;
    return: (![sliceT byteT] "s", SliceSkip byteT (![sliceT byteT] "b") (![uint64T] "l"));;;
    do:  #()).

Definition ReadBool : val :=
  rec: "ReadBool" "b" :=
    exception_do (let: "b" := ref_ty (sliceT byteT) "b" in
    let: "x" := ref_ty boolT (zero_val boolT) in
    let: "$a0" := (![byteT] (slice.elem_ref byteT (![sliceT byteT] "b") #0)) ≠ #(U8 0) in
    do:  "x" <-[boolT] "$a0";;;
    return: (![boolT] "x", SliceSkip byteT (![sliceT byteT] "b") #1);;;
    do:  #()).

Definition ReadLenPrefixedBytes : val :=
  rec: "ReadLenPrefixedBytes" "b" :=
    exception_do (let: "b" := ref_ty (sliceT byteT) "b" in
    let: "b2" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "l" := ref_ty uint64T (zero_val uint64T) in
    let: ("$a0", "$a1") := ReadInt (![sliceT byteT] "b") in
    do:  "b2" <-[sliceT byteT] "$a1";;;
    do:  "l" <-[uint64T] "$a0";;;
    let: "b3" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "bs" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: ("$a0", "$a1") := ReadBytes (![sliceT byteT] "b2") (![uint64T] "l") in
    do:  "b3" <-[sliceT byteT] "$a1";;;
    do:  "bs" <-[sliceT byteT] "$a0";;;
    return: (![sliceT byteT] "bs", ![sliceT byteT] "b3");;;
    do:  #()).

(* WriteInt appends i in little-endian format to b, returning the new slice. *)
Definition WriteInt : val :=
  rec: "WriteInt" "b" "i" :=
    exception_do (let: "i" := ref_ty uint64T "i" in
    let: "b" := ref_ty (sliceT byteT) "b" in
    let: "b2" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := reserve (![sliceT byteT] "b") #8 in
    do:  "b2" <-[sliceT byteT] "$a0";;;
    let: "off" := ref_ty intT (zero_val intT) in
    let: "$a0" := slice.len (![sliceT byteT] "b2") in
    do:  "off" <-[intT] "$a0";;;
    let: "b3" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := SliceTake (![sliceT byteT] "b2") ((![intT] "off") + #8) in
    do:  "b3" <-[sliceT byteT] "$a0";;;
    do:  machine.UInt64Put (SliceSkip byteT (![sliceT byteT] "b3") (![intT] "off")) (![uint64T] "i");;;
    return: (![sliceT byteT] "b3");;;
    do:  #()).

(* WriteInt32 appends 32-bit integer i in little-endian format to b, returning the new slice. *)
Definition WriteInt32 : val :=
  rec: "WriteInt32" "b" "i" :=
    exception_do (let: "i" := ref_ty uint32T "i" in
    let: "b" := ref_ty (sliceT byteT) "b" in
    let: "b2" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := reserve (![sliceT byteT] "b") #4 in
    do:  "b2" <-[sliceT byteT] "$a0";;;
    let: "off" := ref_ty intT (zero_val intT) in
    let: "$a0" := slice.len (![sliceT byteT] "b2") in
    do:  "off" <-[intT] "$a0";;;
    let: "b3" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := SliceTake (![sliceT byteT] "b2") ((![intT] "off") + #4) in
    do:  "b3" <-[sliceT byteT] "$a0";;;
    do:  machine.UInt32Put (SliceSkip byteT (![sliceT byteT] "b3") (![intT] "off")) (![uint32T] "i");;;
    return: (![sliceT byteT] "b3");;;
    do:  #()).

(* Append data to b, returning the new slice. *)
Definition WriteBytes : val :=
  rec: "WriteBytes" "b" "data" :=
    exception_do (let: "data" := ref_ty (sliceT byteT) "data" in
    let: "b" := ref_ty (sliceT byteT) "b" in
    return: (slice.append byteT (![sliceT byteT] "b") (![sliceT byteT] "data"));;;
    do:  #()).

Definition WriteBool : val :=
  rec: "WriteBool" "b" "x" :=
    exception_do (let: "x" := ref_ty boolT "x" in
    let: "b" := ref_ty (sliceT byteT) "b" in
    (if: ![boolT] "x"
    then
      return: (slice.append byteT (![sliceT byteT] "b") (slice.literal byteT [#(U8 1)]));;;
      do:  #()
    else
      return: (slice.append byteT (![sliceT byteT] "b") (slice.literal byteT [#(U8 0)]));;;
      do:  #());;;
    do:  #()).

Definition WriteLenPrefixedBytes : val :=
  rec: "WriteLenPrefixedBytes" "b" "bs" :=
    exception_do (let: "bs" := ref_ty (sliceT byteT) "bs" in
    let: "b" := ref_ty (sliceT byteT) "b" in
    let: "b2" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := WriteInt (![sliceT byteT] "b") (slice.len (![sliceT byteT] "bs")) in
    do:  "b2" <-[sliceT byteT] "$a0";;;
    return: (WriteBytes (![sliceT byteT] "b2") (![sliceT byteT] "bs"));;;
    do:  #()).

End code.
