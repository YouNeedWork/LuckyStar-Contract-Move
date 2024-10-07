
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

type {:datatype} Vec _;

function {:constructor} Vec<T>(v: [int]T, l: int): Vec T;

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := l#Vec(v);
    Vec(v#Vec(v)[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v#Vec(v)[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    l#Vec(v)
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    l#Vec(v) == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(v#Vec(v)[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v#Vec(v)[j] else v#Vec(v)[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} InsertAtVec<T>(v: Vec T, i: int, elem: T): Vec T {
    (var l := l#Vec(v) + 1;
    Vec(
        (lambda j: int ::
         if j >= 0 && j < l then
           if j < i then v#Vec(v)[j]
           else if j > i then v#Vec(v)[j-1] else elem
         else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := l#Vec(v1), v#Vec(v1), l#Vec(v2), v#Vec(v2);
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v);
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v#Vec(v)[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v#Vec(v)[i := elem], l#Vec(v))
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(m[i := m[j]][j := m[i]], l#Vec(v)))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := l#Vec(v);
    (exists i: int :: InRangeVec(v, i) && v#Vec(v)[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

type {:datatype} Multiset _;
function {:constructor} Multiset<T>(v: [T]int, l: int): Multiset T;

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    l#Multiset(s)
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := l#Multiset(s);
    (var cnt := v#Multiset(s)[v];
    Multiset(v#Multiset(s)[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := l#Multiset(s1);
    (var len2 := l#Multiset(s2);
    Multiset((lambda v:T :: v#Multiset(s1)[v]-v#Multiset(s2)[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (l#Multiset(s) == 0) &&
    (forall v: T :: v#Multiset(s)[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (l#Multiset(s1) <= l#Multiset(s2)) &&
    (forall v: T :: v#Multiset(s1)[v] <= v#Multiset(s2)[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    v#Multiset(s)[v] > 0
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

type {:datatype} Table _ _;

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
function {:constructor} Table<K, V>(v: [K]V, e: [K]bool, l: int): Table K V;

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    Table(DefaultTableArray(), DefaultTableKeyExistsArray(), 0)
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    v#Table(t)[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    l#Table(t)
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    e#Table(t)[k]
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    Table(v#Table(t)[k := v], e#Table(t), l#Table(t))
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    Table(v#Table(t)[k := v], e#Table(t)[k := true], l#Table(t) + 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    Table(v#Table(t), e#Table(t)[k := false], l#Table(t) - 1)
}

axiom {:ctor "Table"} (forall<K,V> t: Table K V :: {LenTable(t)}
    (exists k: K :: {ContainsTable(t, k)} ContainsTable(t, k)) ==> LenTable(t) >= 1
);
// TODO: we might want to encoder a stronger property that the length of table
// must be more than N given a set of N items. Currently we don't see a need here
// and the above axiom seems to be sufficient.
// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

// ==================================================================================
// Native address


procedure {:inline 1} $2_address_from_bytes(bytes: Vec (int)) returns (res: int);

procedure {:inline 1} $2_address_to_u256(addr: int) returns (res: int);

procedure {:inline 1} $2_address_from_u256(num: int) returns (res: int);

// ==================================================================================
// Native object


procedure {:inline 1} $2_object_delete_impl(id: int);

procedure {:inline 1} $2_object_record_new_uid(id: int);// ----------------------------------------------------------------------------------
// Native object implementation for object type `$0_vault_Vault'#0_#1'`

procedure {:inline 1} $2_object_borrow_uid'$0_vault_Vault'#0_#1''(obj: $0_vault_Vault'#0_#1') returns (res: $2_object_UID) {
    res := $id#$0_vault_Vault'#0_#1'(obj);
}

function $2_object_$borrow_uid'$0_vault_Vault'#0_#1''(obj: $0_vault_Vault'#0_#1'): $2_object_UID {
    $id#$0_vault_Vault'#0_#1'(obj)
}// ----------------------------------------------------------------------------------
// Native object implementation for object type `$2_coin_Coin'#0'`

procedure {:inline 1} $2_object_borrow_uid'$2_coin_Coin'#0''(obj: $2_coin_Coin'#0') returns (res: $2_object_UID) {
    res := $id#$2_coin_Coin'#0'(obj);
}

function $2_object_$borrow_uid'$2_coin_Coin'#0''(obj: $2_coin_Coin'#0'): $2_object_UID {
    $id#$2_coin_Coin'#0'(obj)
}// ----------------------------------------------------------------------------------
// Native object implementation for object type `$2_coin_Coin'#1'`

procedure {:inline 1} $2_object_borrow_uid'$2_coin_Coin'#1''(obj: $2_coin_Coin'#1') returns (res: $2_object_UID) {
    res := $id#$2_coin_Coin'#1'(obj);
}

function $2_object_$borrow_uid'$2_coin_Coin'#1''(obj: $2_coin_Coin'#1'): $2_object_UID {
    $id#$2_coin_Coin'#1'(obj)
}

// ==================================================================================
// Native tx_context

procedure {:inline 1} $2_tx_context_derive_id(tx_hash: Vec (int), ids_created: int) returns (res: int);

// ==================================================================================
// Native event

// ==================================================================================
// Native types

// ==================================================================================
// Native dynamic_field

procedure {:inline 1} $2_dynamic_field_has_child_object(parent: int, id: int) returns (res: bool);

// ==================================================================================
// Native prover


// ==================================================================================
// Reads and writes to dynamic fields (skeletons)

function GetDynField<T, V>(o: T, addr: int): V;

function UpdateDynField<T, V>(o: T, addr: int, v: V): T;


// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U16: int;
axiom $MAX_U16 == 65535;
const $MAX_U32: int;
axiom $MAX_U32 == 4294967295;
const $MAX_u256: int;
axiom $MAX_u256 == 18446744073709551615;
const $MAX_u256: int;
axiom $MAX_u256 == 340282366920938463463374607431768211455;
const $MAX_U256: int;
axiom $MAX_U256 == 115792089237316195423570985008687907853269984665640564039457584007913129639935;

// Templates for bitvector operations

function {:bvbuiltin "bvand"} $And'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvor"} $Or'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvxor"} $Xor'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvadd"} $Add'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvsub"} $Sub'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvmul"} $Mul'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvudiv"} $Div'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvurem"} $Mod'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvshl"} $Shl'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvlshr"} $Shr'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvult"} $Lt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv8'(bv8,bv8) returns(bool);

procedure {:inline 1} $AddBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Add'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $AddBv8_unchecked(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $SubBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv8'(src1, src2);
}

procedure {:inline 1} $MulBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Mul'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv8'(src1, src2);
}

procedure {:inline 1} $DivBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv8'(src1, src2);
}

procedure {:inline 1} $ModBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv8'(src1, src2);
}

procedure {:inline 1} $AndBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $And'Bv8'(src1,src2);
}

procedure {:inline 1} $OrBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Or'Bv8'(src1,src2);
}

procedure {:inline 1} $XorBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Xor'Bv8'(src1,src2);
}

procedure {:inline 1} $LtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Lt'Bv8'(src1,src2);
}

procedure {:inline 1} $LeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Le'Bv8'(src1,src2);
}

procedure {:inline 1} $GtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Gt'Bv8'(src1,src2);
}

procedure {:inline 1} $GeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Ge'Bv8'(src1,src2);
}

function $IsValid'bv8'(v: bv8): bool {
  $Ge'Bv8'(v,0bv8) && $Le'Bv8'(v,255bv8)
}

function {:inline} $IsEqual'bv8'(x: bv8, y: bv8): bool {
    x == y
}

procedure {:inline 1} $int2bv8(src: int) returns (dst: bv8)
{
    if (src > 255) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.8(src);
}

procedure {:inline 1} $bv2int8(src: bv8) returns (dst: int)
{
    dst := $bv2int.8(src);
}

function {:builtin "(_ int2bv 8)"} $int2bv.8(i: int) returns (bv8);
function {:builtin "bv2nat"} $bv2int.8(i: bv8) returns (int);

function {:bvbuiltin "bvand"} $And'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvor"} $Or'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvxor"} $Xor'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvadd"} $Add'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvsub"} $Sub'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvmul"} $Mul'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvudiv"} $Div'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvurem"} $Mod'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvshl"} $Shl'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvlshr"} $Shr'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvult"} $Lt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv16'(bv16,bv16) returns(bool);

procedure {:inline 1} $AddBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Add'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $AddBv16_unchecked(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $SubBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv16'(src1, src2);
}

procedure {:inline 1} $MulBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Mul'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv16'(src1, src2);
}

procedure {:inline 1} $DivBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv16'(src1, src2);
}

procedure {:inline 1} $ModBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv16'(src1, src2);
}

procedure {:inline 1} $AndBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $And'Bv16'(src1,src2);
}

procedure {:inline 1} $OrBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Or'Bv16'(src1,src2);
}

procedure {:inline 1} $XorBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Xor'Bv16'(src1,src2);
}

procedure {:inline 1} $LtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Lt'Bv16'(src1,src2);
}

procedure {:inline 1} $LeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Le'Bv16'(src1,src2);
}

procedure {:inline 1} $GtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Gt'Bv16'(src1,src2);
}

procedure {:inline 1} $GeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Ge'Bv16'(src1,src2);
}

function $IsValid'bv16'(v: bv16): bool {
  $Ge'Bv16'(v,0bv16) && $Le'Bv16'(v,65535bv16)
}

function {:inline} $IsEqual'bv16'(x: bv16, y: bv16): bool {
    x == y
}

procedure {:inline 1} $int2bv16(src: int) returns (dst: bv16)
{
    if (src > 65535) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.16(src);
}

procedure {:inline 1} $bv2int16(src: bv16) returns (dst: int)
{
    dst := $bv2int.16(src);
}

function {:builtin "(_ int2bv 16)"} $int2bv.16(i: int) returns (bv16);
function {:builtin "bv2nat"} $bv2int.16(i: bv16) returns (int);

function {:bvbuiltin "bvand"} $And'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvor"} $Or'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvxor"} $Xor'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvadd"} $Add'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsub"} $Sub'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvmul"} $Mul'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvudiv"} $Div'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvurem"} $Mod'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvshl"} $Shl'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} $Shr'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvult"} $Lt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv32'(bv32,bv32) returns(bool);

procedure {:inline 1} $AddBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Add'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $AddBv32_unchecked(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $SubBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv32'(src1, src2);
}

procedure {:inline 1} $MulBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Mul'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv32'(src1, src2);
}

procedure {:inline 1} $DivBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv32'(src1, src2);
}

procedure {:inline 1} $ModBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv32'(src1, src2);
}

procedure {:inline 1} $AndBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $And'Bv32'(src1,src2);
}

procedure {:inline 1} $OrBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Or'Bv32'(src1,src2);
}

procedure {:inline 1} $XorBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Xor'Bv32'(src1,src2);
}

procedure {:inline 1} $LtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Lt'Bv32'(src1,src2);
}

procedure {:inline 1} $LeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Le'Bv32'(src1,src2);
}

procedure {:inline 1} $GtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Gt'Bv32'(src1,src2);
}

procedure {:inline 1} $GeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Ge'Bv32'(src1,src2);
}

function $IsValid'bv32'(v: bv32): bool {
  $Ge'Bv32'(v,0bv32) && $Le'Bv32'(v,2147483647bv32)
}

function {:inline} $IsEqual'bv32'(x: bv32, y: bv32): bool {
    x == y
}

procedure {:inline 1} $int2bv32(src: int) returns (dst: bv32)
{
    if (src > 2147483647) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.32(src);
}

procedure {:inline 1} $bv2int32(src: bv32) returns (dst: int)
{
    dst := $bv2int.32(src);
}

function {:builtin "(_ int2bv 32)"} $int2bv.32(i: int) returns (bv32);
function {:builtin "bv2nat"} $bv2int.32(i: bv32) returns (int);

function {:bvbuiltin "bvand"} $And'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvor"} $Or'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvxor"} $Xor'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvadd"} $Add'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsub"} $Sub'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvmul"} $Mul'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvudiv"} $Div'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvurem"} $Mod'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvshl"} $Shl'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvlshr"} $Shr'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvult"} $Lt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv64'(bv64,bv64) returns(bool);

procedure {:inline 1} $AddBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Add'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $AddBv64_unchecked(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $SubBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv64'(src1, src2);
}

procedure {:inline 1} $MulBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Mul'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv64'(src1, src2);
}

procedure {:inline 1} $DivBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv64'(src1, src2);
}

procedure {:inline 1} $ModBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv64'(src1, src2);
}

procedure {:inline 1} $AndBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $And'Bv64'(src1,src2);
}

procedure {:inline 1} $OrBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Or'Bv64'(src1,src2);
}

procedure {:inline 1} $XorBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Xor'Bv64'(src1,src2);
}

procedure {:inline 1} $LtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Lt'Bv64'(src1,src2);
}

procedure {:inline 1} $LeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Le'Bv64'(src1,src2);
}

procedure {:inline 1} $GtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Gt'Bv64'(src1,src2);
}

procedure {:inline 1} $GeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Ge'Bv64'(src1,src2);
}

function $IsValid'bv64'(v: bv64): bool {
  $Ge'Bv64'(v,0bv64) && $Le'Bv64'(v,18446744073709551615bv64)
}

function {:inline} $IsEqual'bv64'(x: bv64, y: bv64): bool {
    x == y
}

procedure {:inline 1} $int2bv64(src: int) returns (dst: bv64)
{
    if (src > 18446744073709551615) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.64(src);
}

procedure {:inline 1} $bv2int64(src: bv64) returns (dst: int)
{
    dst := $bv2int.64(src);
}

function {:builtin "(_ int2bv 64)"} $int2bv.64(i: int) returns (bv64);
function {:builtin "bv2nat"} $bv2int.64(i: bv64) returns (int);

function {:bvbuiltin "bvand"} $And'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvor"} $Or'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvxor"} $Xor'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvadd"} $Add'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvsub"} $Sub'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvmul"} $Mul'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvudiv"} $Div'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvurem"} $Mod'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvshl"} $Shl'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvlshr"} $Shr'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvult"} $Lt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv128'(bv128,bv128) returns(bool);

procedure {:inline 1} $AddBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Add'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $AddBv128_unchecked(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $SubBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv128'(src1, src2);
}

procedure {:inline 1} $MulBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Mul'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv128'(src1, src2);
}

procedure {:inline 1} $DivBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv128'(src1, src2);
}

procedure {:inline 1} $ModBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv128'(src1, src2);
}

procedure {:inline 1} $AndBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $And'Bv128'(src1,src2);
}

procedure {:inline 1} $OrBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Or'Bv128'(src1,src2);
}

procedure {:inline 1} $XorBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Xor'Bv128'(src1,src2);
}

procedure {:inline 1} $LtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Lt'Bv128'(src1,src2);
}

procedure {:inline 1} $LeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Le'Bv128'(src1,src2);
}

procedure {:inline 1} $GtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Gt'Bv128'(src1,src2);
}

procedure {:inline 1} $GeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Ge'Bv128'(src1,src2);
}

function $IsValid'bv128'(v: bv128): bool {
  $Ge'Bv128'(v,0bv128) && $Le'Bv128'(v,340282366920938463463374607431768211455bv128)
}

function {:inline} $IsEqual'bv128'(x: bv128, y: bv128): bool {
    x == y
}

procedure {:inline 1} $int2bv128(src: int) returns (dst: bv128)
{
    if (src > 340282366920938463463374607431768211455) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.128(src);
}

procedure {:inline 1} $bv2int128(src: bv128) returns (dst: int)
{
    dst := $bv2int.128(src);
}

function {:builtin "(_ int2bv 128)"} $int2bv.128(i: int) returns (bv128);
function {:builtin "bv2nat"} $bv2int.128(i: bv128) returns (int);

function {:bvbuiltin "bvand"} $And'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvor"} $Or'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvxor"} $Xor'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvadd"} $Add'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvsub"} $Sub'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvmul"} $Mul'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvudiv"} $Div'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvurem"} $Mod'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvshl"} $Shl'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvlshr"} $Shr'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvult"} $Lt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv256'(bv256,bv256) returns(bool);

procedure {:inline 1} $AddBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Add'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $AddBv256_unchecked(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $SubBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv256'(src1, src2);
}

procedure {:inline 1} $MulBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Mul'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv256'(src1, src2);
}

procedure {:inline 1} $DivBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv256'(src1, src2);
}

procedure {:inline 1} $ModBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv256'(src1, src2);
}

procedure {:inline 1} $AndBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $And'Bv256'(src1,src2);
}

procedure {:inline 1} $OrBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Or'Bv256'(src1,src2);
}

procedure {:inline 1} $XorBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Xor'Bv256'(src1,src2);
}

procedure {:inline 1} $LtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Lt'Bv256'(src1,src2);
}

procedure {:inline 1} $LeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Le'Bv256'(src1,src2);
}

procedure {:inline 1} $GtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Gt'Bv256'(src1,src2);
}

procedure {:inline 1} $GeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Ge'Bv256'(src1,src2);
}

function $IsValid'bv256'(v: bv256): bool {
  $Ge'Bv256'(v,0bv256) && $Le'Bv256'(v,115792089237316195423570985008687907853269984665640564039457584007913129639935bv256)
}

function {:inline} $IsEqual'bv256'(x: bv256, y: bv256): bool {
    x == y
}

procedure {:inline 1} $int2bv256(src: int) returns (dst: bv256)
{
    if (src > 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.256(src);
}

procedure {:inline 1} $bv2int256(src: bv256) returns (dst: int)
{
    dst := $bv2int.256(src);
}

function {:builtin "(_ int2bv 256)"} $int2bv.256(i: int) returns (bv256);
function {:builtin "bv2nat"} $bv2int.256(i: bv256) returns (int);

type {:datatype} $Range;
function {:constructor} $Range(lb: int, ub: int): $Range;

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u16'(v: int): bool {
  v >= 0 && v <= $MAX_U16
}

function $IsValid'u32'(v: int): bool {
  v >= 0 && v <= $MAX_U32
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_u256
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_u256
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U256
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(lb#$Range(r)) &&  $IsValid'u64'(ub#$Range(r))
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   lb#$Range(r) <= i && i < ub#$Range(r)
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u16'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u32'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

type {:datatype} $Location;

// A global resource location within the statically known resource type's memory,
// where `a` is an address.
function {:constructor} $Global(a: int): $Location;

// A local location. `i` is the unique index of the local.
function {:constructor} $Local(i: int): $Location;

// The location of a reference outside of the verification scope, for example, a `&mut` parameter
// of the function being verified. References with these locations don't need to be written back
// when mutation ends.
function {:constructor} $Param(i: int): $Location;

// The location of an uninitialized mutation. Using this to make sure that the location
// will not be equal to any valid mutation locations, i.e., $Local, $Global, or $Param.
function {:constructor} $Uninitialized(): $Location;

// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
type {:datatype} $Mutation _;
function {:constructor} $Mutation<T>(l: $Location, p: Vec int, v: T): $Mutation T;

// Representation of memory for a given type.
type {:datatype} $Memory _;
function {:constructor} $Memory<T>(domain: [int]bool, contents: [int]T): $Memory T;

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    v#$Mutation(ref)
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(l#$Mutation(m), p#$Mutation(m), v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), offset), v)
}

// Return true if two mutations share the location and path
function {:inline} $IsSameMutation<T1, T2>(parent: $Mutation T1, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) && p#$Mutation(parent) == p#$Mutation(child)
}

// Return true if the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true if the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    l#$Mutation(m1) == l#$Mutation(m2)
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    is#$Global(l#$Mutation(m))
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    l#$Mutation(m) == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    a#$Global(l#$Mutation(m))
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    domain#$Memory(m)[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    contents#$Memory(m)[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(domain#$Memory(m)[a := true], contents#$Memory(m)[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := false], contents#$Memory(m))
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := domain#$Memory(s)[a]],
            contents#$Memory(m)[a := contents#$Memory(s)[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU16(src: int) returns (dst: int)
{
    if (src > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU32(src: int) returns (dst: int)
{
    if (src > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $Castu256(src: int) returns (dst: int)
{
    if (src > $MAX_u256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $Castu256(src: int) returns (dst: int)
{
    if (src > $MAX_u256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU256(src: int) returns (dst: int)
{
    if (src > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Addu256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_u256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $Addu256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Addu256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_u256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $Addu256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shlU8(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 256
}

function $shlU16(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 65536
}

function $shlU32(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 4294967296
}

function $shlu256(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 18446744073709551616
}

function $shlu256(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 340282366920938463463374607431768211456
}

function $shlU256(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 115792089237316195423570985008687907853269984665640564039457584007913129639936
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

// We need to know the size of the destination in order to drop bits
// that have been shifted left more than that, so we have $ShlU8/16/32/64/128/256
procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU8(src1, src2);
}

// Template for cast and shift operations of bitvector types

procedure {:inline 1} $CastBv8to8(src: bv8) returns (dst: bv8)
{
    dst := src;
}


function $shlBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shl'Bv8'(src1, src2)
}

procedure {:inline 1} $ShlBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2);
}

function $shrBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shr'Bv8'(src1, src2)
}

procedure {:inline 1} $ShrBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2);
}

procedure {:inline 1} $CastBv16to8(src: bv16) returns (dst: bv8)
{
    if ($Gt'Bv16'(src, 255bv16)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv32to8(src: bv32) returns (dst: bv8)
{
    if ($Gt'Bv32'(src, 255bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv64to8(src: bv64) returns (dst: bv8)
{
    if ($Gt'Bv64'(src, 255bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv128to8(src: bv128) returns (dst: bv8)
{
    if ($Gt'Bv128'(src, 255bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv256to8(src: bv256) returns (dst: bv8)
{
    if ($Gt'Bv256'(src, 255bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv8to16(src: bv8) returns (dst: bv16)
{
    dst := 0bv8 ++ src;
}


function $shlBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shl'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShlBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, 0bv8 ++ src2);
}

function $shrBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shr'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShrBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, 0bv8 ++ src2);
}

procedure {:inline 1} $CastBv16to16(src: bv16) returns (dst: bv16)
{
    dst := src;
}


function $shlBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shl'Bv16'(src1, src2)
}

procedure {:inline 1} $ShlBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2);
}

function $shrBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shr'Bv16'(src1, src2)
}

procedure {:inline 1} $ShrBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2);
}

procedure {:inline 1} $CastBv32to16(src: bv32) returns (dst: bv16)
{
    if ($Gt'Bv32'(src, 65535bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv64to16(src: bv64) returns (dst: bv16)
{
    if ($Gt'Bv64'(src, 65535bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv128to16(src: bv128) returns (dst: bv16)
{
    if ($Gt'Bv128'(src, 65535bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv256to16(src: bv256) returns (dst: bv16)
{
    if ($Gt'Bv256'(src, 65535bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv8to32(src: bv8) returns (dst: bv32)
{
    dst := 0bv24 ++ src;
}


function $shlBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShlBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv24 ++ src2);
}

function $shrBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShrBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv24 ++ src2);
}

procedure {:inline 1} $CastBv16to32(src: bv16) returns (dst: bv32)
{
    dst := 0bv16 ++ src;
}


function $shlBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShlBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv16 ++ src2);
}

function $shrBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShrBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv16 ++ src2);
}

procedure {:inline 1} $CastBv32to32(src: bv32) returns (dst: bv32)
{
    dst := src;
}


function $shlBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shl'Bv32'(src1, src2)
}

procedure {:inline 1} $ShlBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2);
}

function $shrBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shr'Bv32'(src1, src2)
}

procedure {:inline 1} $ShrBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2);
}

procedure {:inline 1} $CastBv64to32(src: bv64) returns (dst: bv32)
{
    if ($Gt'Bv64'(src, 2147483647bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv128to32(src: bv128) returns (dst: bv32)
{
    if ($Gt'Bv128'(src, 2147483647bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv256to32(src: bv256) returns (dst: bv32)
{
    if ($Gt'Bv256'(src, 2147483647bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv8to64(src: bv8) returns (dst: bv64)
{
    dst := 0bv56 ++ src;
}


function $shlBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShlBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv56 ++ src2);
}

function $shrBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShrBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv56 ++ src2);
}

procedure {:inline 1} $CastBv16to64(src: bv16) returns (dst: bv64)
{
    dst := 0bv48 ++ src;
}


function $shlBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShlBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv48 ++ src2);
}

function $shrBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShrBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv48 ++ src2);
}

procedure {:inline 1} $CastBv32to64(src: bv32) returns (dst: bv64)
{
    dst := 0bv32 ++ src;
}


function $shlBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShlBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv32 ++ src2);
}

function $shrBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShrBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv32 ++ src2);
}

procedure {:inline 1} $CastBv64to64(src: bv64) returns (dst: bv64)
{
    dst := src;
}


function $shlBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shl'Bv64'(src1, src2)
}

procedure {:inline 1} $ShlBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2);
}

function $shrBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shr'Bv64'(src1, src2)
}

procedure {:inline 1} $ShrBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2);
}

procedure {:inline 1} $CastBv128to64(src: bv128) returns (dst: bv64)
{
    if ($Gt'Bv128'(src, 18446744073709551615bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv256to64(src: bv256) returns (dst: bv64)
{
    if ($Gt'Bv256'(src, 18446744073709551615bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv8to128(src: bv8) returns (dst: bv128)
{
    dst := 0bv120 ++ src;
}


function $shlBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShlBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv120 ++ src2);
}

function $shrBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShrBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv120 ++ src2);
}

procedure {:inline 1} $CastBv16to128(src: bv16) returns (dst: bv128)
{
    dst := 0bv112 ++ src;
}


function $shlBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShlBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv112 ++ src2);
}

function $shrBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShrBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv112 ++ src2);
}

procedure {:inline 1} $CastBv32to128(src: bv32) returns (dst: bv128)
{
    dst := 0bv96 ++ src;
}


function $shlBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShlBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv96 ++ src2);
}

function $shrBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShrBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv96 ++ src2);
}

procedure {:inline 1} $CastBv64to128(src: bv64) returns (dst: bv128)
{
    dst := 0bv64 ++ src;
}


function $shlBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShlBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv64 ++ src2);
}

function $shrBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShrBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv64 ++ src2);
}

procedure {:inline 1} $CastBv128to128(src: bv128) returns (dst: bv128)
{
    dst := src;
}


function $shlBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shl'Bv128'(src1, src2)
}

procedure {:inline 1} $ShlBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2);
}

function $shrBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shr'Bv128'(src1, src2)
}

procedure {:inline 1} $ShrBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2);
}

procedure {:inline 1} $CastBv256to128(src: bv256) returns (dst: bv128)
{
    if ($Gt'Bv256'(src, 340282366920938463463374607431768211455bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[128:0];
}


function $shlBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shl'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShlBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2[128:0]);
}

function $shrBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shr'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShrBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2[128:0]);
}

procedure {:inline 1} $CastBv8to256(src: bv8) returns (dst: bv256)
{
    dst := 0bv248 ++ src;
}


function $shlBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShlBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv248 ++ src2);
}

function $shrBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShrBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv248 ++ src2);
}

procedure {:inline 1} $CastBv16to256(src: bv16) returns (dst: bv256)
{
    dst := 0bv240 ++ src;
}


function $shlBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShlBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv240 ++ src2);
}

function $shrBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShrBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv240 ++ src2);
}

procedure {:inline 1} $CastBv32to256(src: bv32) returns (dst: bv256)
{
    dst := 0bv224 ++ src;
}


function $shlBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShlBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv224 ++ src2);
}

function $shrBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShrBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv224 ++ src2);
}

procedure {:inline 1} $CastBv64to256(src: bv64) returns (dst: bv256)
{
    dst := 0bv192 ++ src;
}


function $shlBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShlBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv192 ++ src2);
}

function $shrBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShrBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv192 ++ src2);
}

procedure {:inline 1} $CastBv128to256(src: bv128) returns (dst: bv256)
{
    dst := 0bv128 ++ src;
}


function $shlBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShlBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv128 ++ src2);
}

function $shrBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShrBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv128 ++ src2);
}

procedure {:inline 1} $CastBv256to256(src: bv256) returns (dst: bv256)
{
    dst := src;
}


function $shlBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shl'Bv256'(src1, src2)
}

procedure {:inline 1} $ShlBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, src2);
}

function $shrBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shr'Bv256'(src1, src2)
}

procedure {:inline 1} $ShrBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, src2);
}

procedure {:inline 1} $ShlU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU16(src1, src2);
}

procedure {:inline 1} $ShlU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU32(src1, src2);
}

procedure {:inline 1} $Shlu256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
       call $ExecFailureAbort();
       return;
    }
    dst := $shlu256(src1, src2);
}

procedure {:inline 1} $Shlu256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlu256(src1, src2);
}

procedure {:inline 1} $ShlU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shlU256(src1, src2);
}

procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $Shru256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $Shru256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Mulu256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_u256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Mulu256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_u256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, lb#$Range(r), ub#$Range(r))
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$2_vec_map_Entry'address_u256'`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$2_vec_map_Entry'address_u256'''(v1: Vec ($2_vec_map_Entry'address_u256'), v2: Vec ($2_vec_map_Entry'address_u256')): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$2_vec_map_Entry'address_u256''(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$2_vec_map_Entry'address_u256'''(v: Vec ($2_vec_map_Entry'address_u256'), prefix: Vec ($2_vec_map_Entry'address_u256')): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$2_vec_map_Entry'address_u256''(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$2_vec_map_Entry'address_u256'''(v: Vec ($2_vec_map_Entry'address_u256'), suffix: Vec ($2_vec_map_Entry'address_u256')): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$2_vec_map_Entry'address_u256''(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$2_vec_map_Entry'address_u256'''(v: Vec ($2_vec_map_Entry'address_u256')): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$2_vec_map_Entry'address_u256''(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256'), e: $2_vec_map_Entry'address_u256'): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$2_vec_map_Entry'address_u256''(ReadVec(v, i), e))
}

function $IndexOfVec'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256'), e: $2_vec_map_Entry'address_u256'): int;
axiom (forall v: Vec ($2_vec_map_Entry'address_u256'), e: $2_vec_map_Entry'address_u256':: {$IndexOfVec'$2_vec_map_Entry'address_u256''(v, e)}
    (var i := $IndexOfVec'$2_vec_map_Entry'address_u256''(v, e);
     if (!$ContainsVec'$2_vec_map_Entry'address_u256''(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$2_vec_map_Entry'address_u256''(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$2_vec_map_Entry'address_u256''(ReadVec(v, j), e))));


function {:inline} $RangeVec'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256')): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$2_vec_map_Entry'address_u256''(): Vec ($2_vec_map_Entry'address_u256') {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$2_vec_map_Entry'address_u256''() returns (v: Vec ($2_vec_map_Entry'address_u256')) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$2_vec_map_Entry'address_u256''(): Vec ($2_vec_map_Entry'address_u256') {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256')) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$2_vec_map_Entry'address_u256''(m: $Mutation (Vec ($2_vec_map_Entry'address_u256')), val: $2_vec_map_Entry'address_u256') returns (m': $Mutation (Vec ($2_vec_map_Entry'address_u256'))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256'), val: $2_vec_map_Entry'address_u256'): Vec ($2_vec_map_Entry'address_u256') {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$2_vec_map_Entry'address_u256''(m: $Mutation (Vec ($2_vec_map_Entry'address_u256'))) returns (e: $2_vec_map_Entry'address_u256', m': $Mutation (Vec ($2_vec_map_Entry'address_u256'))) {
    var v: Vec ($2_vec_map_Entry'address_u256');
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'$2_vec_map_Entry'address_u256''(m: $Mutation (Vec ($2_vec_map_Entry'address_u256')), other: Vec ($2_vec_map_Entry'address_u256')) returns (m': $Mutation (Vec ($2_vec_map_Entry'address_u256'))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$2_vec_map_Entry'address_u256''(m: $Mutation (Vec ($2_vec_map_Entry'address_u256'))) returns (m': $Mutation (Vec ($2_vec_map_Entry'address_u256'))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_length'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256')) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256')): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256'), i: int) returns (dst: $2_vec_map_Entry'address_u256') {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256'), i: int): $2_vec_map_Entry'address_u256' {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$2_vec_map_Entry'address_u256''(m: $Mutation (Vec ($2_vec_map_Entry'address_u256')), index: int)
returns (dst: $Mutation ($2_vec_map_Entry'address_u256'), m': $Mutation (Vec ($2_vec_map_Entry'address_u256')))
{
    var v: Vec ($2_vec_map_Entry'address_u256');
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256'), i: int): $2_vec_map_Entry'address_u256' {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256')) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$2_vec_map_Entry'address_u256''(m: $Mutation (Vec ($2_vec_map_Entry'address_u256')), i: int, j: int) returns (m': $Mutation (Vec ($2_vec_map_Entry'address_u256')))
{
    var v: Vec ($2_vec_map_Entry'address_u256');
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256'), i: int, j: int): Vec ($2_vec_map_Entry'address_u256') {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$2_vec_map_Entry'address_u256''(m: $Mutation (Vec ($2_vec_map_Entry'address_u256')), i: int) returns (e: $2_vec_map_Entry'address_u256', m': $Mutation (Vec ($2_vec_map_Entry'address_u256')))
{
    var v: Vec ($2_vec_map_Entry'address_u256');

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_insert'$2_vec_map_Entry'address_u256''(m: $Mutation (Vec ($2_vec_map_Entry'address_u256')), val: $2_vec_map_Entry'address_u256', i: int) returns (m': $Mutation (Vec ($2_vec_map_Entry'address_u256'))) {

    var len: int;
    var v: Vec ($2_vec_map_Entry'address_u256');

    v := $Dereference(m);

    len := LenVec(v);
    if (i < 0 || i > len) {
        call $ExecFailureAbort();
        return;
    }
    if (i == len) {
        m' := $UpdateMutation(m, ExtendVec(v, val));
    } else {
        m' := $UpdateMutation(m, InsertAtVec(v, i, val));
    }
}

procedure {:inline 1} $1_vector_swap_remove'$2_vec_map_Entry'address_u256''(m: $Mutation (Vec ($2_vec_map_Entry'address_u256')), i: int) returns (e: $2_vec_map_Entry'address_u256', m': $Mutation (Vec ($2_vec_map_Entry'address_u256')))
{
    var len: int;
    var v: Vec ($2_vec_map_Entry'address_u256');

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256'), e: $2_vec_map_Entry'address_u256') returns (res: bool)  {
    res := $ContainsVec'$2_vec_map_Entry'address_u256''(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$2_vec_map_Entry'address_u256''(v: Vec ($2_vec_map_Entry'address_u256'), e: $2_vec_map_Entry'address_u256') returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$2_vec_map_Entry'address_u256''(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u8''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u8''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_insert'u8'(m: $Mutation (Vec (int)), val: int, i: int) returns (m': $Mutation (Vec (int))) {

    var len: int;
    var v: Vec (int);

    v := $Dereference(m);

    len := LenVec(v);
    if (i < 0 || i > len) {
        call $ExecFailureAbort();
        return;
    }
    if (i == len) {
        m' := $UpdateMutation(m, ExtendVec(v, val));
    } else {
        m' := $UpdateMutation(m, InsertAtVec(v, i, val));
    }
}

procedure {:inline 1} $1_vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `bv8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'bv8''(v1: Vec (bv8), v2: Vec (bv8)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'bv8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'bv8''(v: Vec (bv8), prefix: Vec (bv8)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'bv8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'bv8''(v: Vec (bv8), suffix: Vec (bv8)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'bv8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'bv8''(v: Vec (bv8)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'bv8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'bv8'(v: Vec (bv8), e: bv8): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv8'(ReadVec(v, i), e))
}

function $IndexOfVec'bv8'(v: Vec (bv8), e: bv8): int;
axiom (forall v: Vec (bv8), e: bv8:: {$IndexOfVec'bv8'(v, e)}
    (var i := $IndexOfVec'bv8'(v, e);
     if (!$ContainsVec'bv8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'bv8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'bv8'(v: Vec (bv8)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'bv8'(): Vec (bv8) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'bv8'() returns (v: Vec (bv8)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'bv8'(): Vec (bv8) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'bv8'(v: Vec (bv8)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'bv8'(m: $Mutation (Vec (bv8)), val: bv8) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'bv8'(v: Vec (bv8), val: bv8): Vec (bv8) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'bv8'(m: $Mutation (Vec (bv8))) returns (e: bv8, m': $Mutation (Vec (bv8))) {
    var v: Vec (bv8);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'bv8'(m: $Mutation (Vec (bv8)), other: Vec (bv8)) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'bv8'(m: $Mutation (Vec (bv8))) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_length'bv8'(v: Vec (bv8)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'bv8'(v: Vec (bv8)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'bv8'(v: Vec (bv8), i: int) returns (dst: bv8) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'bv8'(v: Vec (bv8), i: int): bv8 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'bv8'(m: $Mutation (Vec (bv8)), index: int)
returns (dst: $Mutation (bv8), m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'bv8'(v: Vec (bv8), i: int): bv8 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'bv8'(v: Vec (bv8)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'bv8'(m: $Mutation (Vec (bv8)), i: int, j: int) returns (m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'bv8'(v: Vec (bv8), i: int, j: int): Vec (bv8) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'bv8'(m: $Mutation (Vec (bv8)), i: int) returns (e: bv8, m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_insert'bv8'(m: $Mutation (Vec (bv8)), val: bv8, i: int) returns (m': $Mutation (Vec (bv8))) {

    var len: int;
    var v: Vec (bv8);

    v := $Dereference(m);

    len := LenVec(v);
    if (i < 0 || i > len) {
        call $ExecFailureAbort();
        return;
    }
    if (i == len) {
        m' := $UpdateMutation(m, ExtendVec(v, val));
    } else {
        m' := $UpdateMutation(m, InsertAtVec(v, i, val));
    }
}

procedure {:inline 1} $1_vector_swap_remove'bv8'(m: $Mutation (Vec (bv8)), i: int) returns (e: bv8, m': $Mutation (Vec (bv8)))
{
    var len: int;
    var v: Vec (bv8);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'bv8'(v: Vec (bv8), e: bv8) returns (res: bool)  {
    res := $ContainsVec'bv8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'bv8'(v: Vec (bv8), e: bv8) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'bv8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Table

// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native string

// TODO: correct implementation of strings

procedure {:inline 1} $1_string_internal_check_utf8(x: Vec int) returns (r: bool) {
}

procedure {:inline 1} $1_string_internal_sub_string(x: Vec int, i: int, j: int) returns (r: Vec int) {
}

procedure {:inline 1} $1_string_internal_index_of(x: Vec int, y: Vec int) returns (r: int) {
}

procedure {:inline 1} $1_string_internal_is_char_boundary(x: Vec int, i: int) returns (r: bool) {
}




// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

type {:datatype} $signer;
function {:constructor} $signer($addr: int): $signer;
function {:inline} $IsValid'signer'(s: $signer): bool {
    $IsValid'address'($addr#$signer(s))
}
function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    s1 == s2
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := $addr#$signer(signer);
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    $addr#$signer(signer)
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize

// ----------------------------------------------------------------------------------
// Native BCS implementation for element type `$2_tx_context_TxContext`

// Serialize is modeled as an uninterpreted function, with an additional
// axiom to say it's an injection.

function $1_bcs_serialize'$2_tx_context_TxContext'(v: $2_tx_context_TxContext): Vec int;

axiom (forall v1, v2: $2_tx_context_TxContext :: {$1_bcs_serialize'$2_tx_context_TxContext'(v1), $1_bcs_serialize'$2_tx_context_TxContext'(v2)}
   $IsEqual'$2_tx_context_TxContext'(v1, v2) <==> $IsEqual'vec'u8''($1_bcs_serialize'$2_tx_context_TxContext'(v1), $1_bcs_serialize'$2_tx_context_TxContext'(v2)));

// This says that serialize returns a non-empty vec<u8>

axiom (forall v: $2_tx_context_TxContext :: {$1_bcs_serialize'$2_tx_context_TxContext'(v)}
     ( var r := $1_bcs_serialize'$2_tx_context_TxContext'(v); $IsValid'vec'u8''(r) && LenVec(r) > 0 ));


procedure $1_bcs_to_bytes'$2_tx_context_TxContext'(v: $2_tx_context_TxContext) returns (res: Vec int);
ensures res == $1_bcs_serialize'$2_tx_context_TxContext'(v);

function {:inline} $1_bcs_$to_bytes'$2_tx_context_TxContext'(v: $2_tx_context_TxContext): Vec int {
    $1_bcs_serialize'$2_tx_context_TxContext'(v)
}




// ----------------------------------------------------------------------------------
// Native BCS implementation for element type `address`

// Serialize is modeled as an uninterpreted function, with an additional
// axiom to say it's an injection.

function $1_bcs_serialize'address'(v: int): Vec int;

axiom (forall v1, v2: int :: {$1_bcs_serialize'address'(v1), $1_bcs_serialize'address'(v2)}
   $IsEqual'address'(v1, v2) <==> $IsEqual'vec'u8''($1_bcs_serialize'address'(v1), $1_bcs_serialize'address'(v2)));

// This says that serialize returns a non-empty vec<u8>

axiom (forall v: int :: {$1_bcs_serialize'address'(v)}
     ( var r := $1_bcs_serialize'address'(v); $IsValid'vec'u8''(r) && LenVec(r) > 0 ));


procedure $1_bcs_to_bytes'address'(v: int) returns (res: Vec int);
ensures res == $1_bcs_serialize'address'(v);

function {:inline} $1_bcs_$to_bytes'address'(v: int): Vec int {
    $1_bcs_serialize'address'(v)
}

// Serialized addresses should have the same length.
const $serialized_address_len: int;
// Serialized addresses should have the same length
axiom (forall v: int :: {$1_bcs_serialize'address'(v)}
     ( var r := $1_bcs_serialize'address'(v); LenVec(r) == $serialized_address_len));




// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}

// ============================================================================================
// Type Reflection on Type Parameters

type {:datatype} $TypeParamInfo;

function {:constructor} $TypeParamBool(): $TypeParamInfo;
function {:constructor} $TypeParamU8(): $TypeParamInfo;
function {:constructor} $TypeParamU16(): $TypeParamInfo;
function {:constructor} $TypeParamU32(): $TypeParamInfo;
function {:constructor} $TypeParamu256(): $TypeParamInfo;
function {:constructor} $TypeParamu256(): $TypeParamInfo;
function {:constructor} $TypeParamU256(): $TypeParamInfo;
function {:constructor} $TypeParamAddress(): $TypeParamInfo;
function {:constructor} $TypeParamSigner(): $TypeParamInfo;
function {:constructor} $TypeParamVector(e: $TypeParamInfo): $TypeParamInfo;
function {:constructor} $TypeParamStruct(a: int, m: Vec int, s: Vec int): $TypeParamInfo;



//==================================
// Begin Translation

function $TypeName(t: $TypeParamInfo): Vec int;
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamBool(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)) ==> is#$TypeParamBool(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU8(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)) ==> is#$TypeParamU8(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU16(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)) ==> is#$TypeParamU16(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU32(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)) ==> is#$TypeParamU32(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamu256(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)) ==> is#$TypeParamu256(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamu256(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)) ==> is#$TypeParamu256(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU256(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)) ==> is#$TypeParamU256(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamAddress(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)) ==> is#$TypeParamAddress(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamSigner(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)) ==> is#$TypeParamSigner(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamVector(t) ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7), $TypeName(e#$TypeParamVector(t))), Vec(DefaultVecMap()[0 := 62], 1))));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} ($IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7)) && $IsSuffix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 62], 1))) ==> is#$TypeParamVector(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamStruct(t) ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 48][1 := 120], 2), MakeVec1(a#$TypeParamStruct(t))), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), m#$TypeParamStruct(t)), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), s#$TypeParamStruct(t))));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 48][1 := 120], 2)) ==> is#$TypeParamVector(t));


// Given Types for Type Parameters

type {:datatype} #0;
function {:constructor} #0($id: $2_object_UID): #0;
function {:inline} $IsEqual'#0'(x1: #0, x2: #0): bool { x1 == x2 }
function {:inline} $IsValid'#0'(x: #0): bool { true }
var #0_info: $TypeParamInfo;
type {:datatype} #1;
function {:constructor} #1($id: $2_object_UID): #1;
function {:inline} $IsEqual'#1'(x1: #1, x2: #1): bool { x1 == x2 }
function {:inline} $IsValid'#1'(x: #1): bool { true }
var #1_info: $TypeParamInfo;

// struct tx_context::TxContext at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:22:5+514
type {:datatype} $2_tx_context_TxContext;
function {:constructor} $2_tx_context_TxContext($sender: int, $tx_hash: Vec (int), $epoch: int, $epoch_timestamp_ms: int, $ids_created: int): $2_tx_context_TxContext;
function {:inline} $Update'$2_tx_context_TxContext'_sender(s: $2_tx_context_TxContext, x: int): $2_tx_context_TxContext {
    $2_tx_context_TxContext(x, $tx_hash#$2_tx_context_TxContext(s), $epoch#$2_tx_context_TxContext(s), $epoch_timestamp_ms#$2_tx_context_TxContext(s), $ids_created#$2_tx_context_TxContext(s))
}
function {:inline} $Update'$2_tx_context_TxContext'_tx_hash(s: $2_tx_context_TxContext, x: Vec (int)): $2_tx_context_TxContext {
    $2_tx_context_TxContext($sender#$2_tx_context_TxContext(s), x, $epoch#$2_tx_context_TxContext(s), $epoch_timestamp_ms#$2_tx_context_TxContext(s), $ids_created#$2_tx_context_TxContext(s))
}
function {:inline} $Update'$2_tx_context_TxContext'_epoch(s: $2_tx_context_TxContext, x: int): $2_tx_context_TxContext {
    $2_tx_context_TxContext($sender#$2_tx_context_TxContext(s), $tx_hash#$2_tx_context_TxContext(s), x, $epoch_timestamp_ms#$2_tx_context_TxContext(s), $ids_created#$2_tx_context_TxContext(s))
}
function {:inline} $Update'$2_tx_context_TxContext'_epoch_timestamp_ms(s: $2_tx_context_TxContext, x: int): $2_tx_context_TxContext {
    $2_tx_context_TxContext($sender#$2_tx_context_TxContext(s), $tx_hash#$2_tx_context_TxContext(s), $epoch#$2_tx_context_TxContext(s), x, $ids_created#$2_tx_context_TxContext(s))
}
function {:inline} $Update'$2_tx_context_TxContext'_ids_created(s: $2_tx_context_TxContext, x: int): $2_tx_context_TxContext {
    $2_tx_context_TxContext($sender#$2_tx_context_TxContext(s), $tx_hash#$2_tx_context_TxContext(s), $epoch#$2_tx_context_TxContext(s), $epoch_timestamp_ms#$2_tx_context_TxContext(s), x)
}
function $IsValid'$2_tx_context_TxContext'(s: $2_tx_context_TxContext): bool {
    $IsValid'address'($sender#$2_tx_context_TxContext(s))
      && $IsValid'vec'u8''($tx_hash#$2_tx_context_TxContext(s))
      && $IsValid'u64'($epoch#$2_tx_context_TxContext(s))
      && $IsValid'u64'($epoch_timestamp_ms#$2_tx_context_TxContext(s))
      && $IsValid'u64'($ids_created#$2_tx_context_TxContext(s))
}
function {:inline} $IsEqual'$2_tx_context_TxContext'(s1: $2_tx_context_TxContext, s2: $2_tx_context_TxContext): bool {
    $IsEqual'address'($sender#$2_tx_context_TxContext(s1), $sender#$2_tx_context_TxContext(s2))
    && $IsEqual'vec'u8''($tx_hash#$2_tx_context_TxContext(s1), $tx_hash#$2_tx_context_TxContext(s2))
    && $IsEqual'u64'($epoch#$2_tx_context_TxContext(s1), $epoch#$2_tx_context_TxContext(s2))
    && $IsEqual'u64'($epoch_timestamp_ms#$2_tx_context_TxContext(s1), $epoch_timestamp_ms#$2_tx_context_TxContext(s2))
    && $IsEqual'u64'($ids_created#$2_tx_context_TxContext(s1), $ids_created#$2_tx_context_TxContext(s2))}

// fun tx_context::fresh_object_address [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:55:5+222
procedure {:inline 1} $2_tx_context_fresh_object_address(_$t0: $Mutation ($2_tx_context_TxContext)) returns ($ret0: int, $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: Vec (int);
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: $Mutation (int);
    var $t0: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[ctx]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:55:5+1
    assume {:print "$at(69,1918,1919)"} true;
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(0,3,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t3 := get_field<tx_context::TxContext>.ids_created($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:56:27+15
    assume {:print "$at(69,2008,2023)"} true;
    $t3 := $ids_created#$2_tx_context_TxContext($Dereference($t0));

    // trace_local[ids_created#1#0]($t3) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:56:13+11
    assume {:print "$track_local(0,3,2):", $t3} $t3 == $t3;

    // $t4 := get_field<tx_context::TxContext>.tx_hash($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:57:29+12
    assume {:print "$at(69,2053,2065)"} true;
    $t4 := $tx_hash#$2_tx_context_TxContext($Dereference($t0));

    // $t5 := opaque begin: tx_context::derive_id($t4, $t3) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:57:18+37

    // assume WellFormed($t5) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:57:18+37
    assume $IsValid'address'($t5);

    // $t5 := opaque end: tx_context::derive_id($t4, $t3) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:57:18+37

    // trace_local[id#1#0]($t5) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:57:13+2
    assume {:print "$track_local(0,3,1):", $t5} $t5 == $t5;

    // $t6 := 1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:58:41+1
    assume {:print "$at(69,2121,2122)"} true;
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := +($t3, $t6) on_abort goto L2 with $t8 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:58:39+1
    call $t7 := $Addu256($t3, $t6);
    if ($abort_flag) {
        assume {:print "$at(69,2119,2120)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(0,3):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t9 := borrow_field<tx_context::TxContext>.ids_created($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:58:9+15
    $t9 := $ChildMutation($t0, 4, $ids_created#$2_tx_context_TxContext($Dereference($t0)));

    // write_ref($t9, $t7) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:58:9+33
    $t9 := $UpdateMutation($t9, $t7);

    // write_back[Reference($t0).ids_created (u64)]($t9) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:58:9+33
    $t0 := $UpdateMutation($t0, $Update'$2_tx_context_TxContext'_ids_created($Dereference($t0), $Dereference($t9)));

    // trace_local[ctx]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:58:9+33
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(0,3,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // trace_return[0]($t5) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:59:9+2
    assume {:print "$at(69,2132,2134)"} true;
    assume {:print "$track_return(0,3,0):", $t5} $t5 == $t5;

    // trace_local[ctx]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:59:9+2
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(0,3,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:60:5+1
    assume {:print "$at(69,2139,2140)"} true;
L1:

    // return $t5 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:60:5+1
    assume {:print "$at(69,2139,2140)"} true;
    $ret0 := $t5;
    $ret1 := $t0;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:60:5+1
L2:

    // abort($t8) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:60:5+1
    assume {:print "$at(69,2139,2140)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun tx_context::sender [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:38:5+72
procedure {:inline 1} $2_tx_context_sender(_$t0: $2_tx_context_TxContext) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t0: $2_tx_context_TxContext;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'address': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:38:5+1
    assume {:print "$at(69,1352,1353)"} true;
    assume {:print "$track_local(0,0,0):", $t0} $t0 == $t0;

    // $t1 := get_field<tx_context::TxContext>.sender($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:39:9+11
    assume {:print "$at(69,1407,1418)"} true;
    $t1 := $sender#$2_tx_context_TxContext($t0);

    // trace_return[0]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:39:9+11
    assume {:print "$track_return(0,0,0):", $t1} $t1 == $t1;

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:40:5+1
    assume {:print "$at(69,1423,1424)"} true;
L1:

    // return $t1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/tx_context.move:40:5+1
    assume {:print "$at(69,1423,1424)"} true;
    $ret0 := $t1;
    return;

}

// spec fun at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:133:5+69
function {:inline} $2_object_$id'$2_coin_Coin'#0''(obj: $2_coin_Coin'#0'): $2_object_ID {
    $id#$2_object_UID($2_object_$borrow_uid'$2_coin_Coin'#0''(obj))
}

// spec fun at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:133:5+69
function {:inline} $2_object_$id'$2_coin_Coin'#1''(obj: $2_coin_Coin'#1'): $2_object_ID {
    $id#$2_object_UID($2_object_$borrow_uid'$2_coin_Coin'#1''(obj))
}

// spec fun at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:133:5+69
function {:inline} $2_object_$id'$0_vault_Vault'#0_#1''(obj: $0_vault_Vault'#0_#1'): $2_object_ID {
    $id#$2_object_UID($2_object_$borrow_uid'$0_vault_Vault'#0_#1''(obj))
}

// struct object::ID at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:33:5+406
type {:datatype} $2_object_ID;
function {:constructor} $2_object_ID($bytes: int): $2_object_ID;
function {:inline} $Update'$2_object_ID'_bytes(s: $2_object_ID, x: int): $2_object_ID {
    $2_object_ID(x)
}
function $IsValid'$2_object_ID'(s: $2_object_ID): bool {
    $IsValid'address'($bytes#$2_object_ID(s))
}
function {:inline} $IsEqual'$2_object_ID'(s1: $2_object_ID, s2: $2_object_ID): bool {
    s1 == s2
}

// struct object::Ownership at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:227:5+112
type {:datatype} $2_object_Ownership;
function {:constructor} $2_object_Ownership($owner: int, $status: int): $2_object_Ownership;
function {:inline} $Update'$2_object_Ownership'_owner(s: $2_object_Ownership, x: int): $2_object_Ownership {
    $2_object_Ownership(x, $status#$2_object_Ownership(s))
}
function {:inline} $Update'$2_object_Ownership'_status(s: $2_object_Ownership, x: int): $2_object_Ownership {
    $2_object_Ownership($owner#$2_object_Ownership(s), x)
}
function $IsValid'$2_object_Ownership'(s: $2_object_Ownership): bool {
    $IsValid'address'($owner#$2_object_Ownership(s))
      && $IsValid'u64'($status#$2_object_Ownership(s))
}
function {:inline} $IsEqual'$2_object_Ownership'(s1: $2_object_Ownership, s2: $2_object_Ownership): bool {
    s1 == s2
}
var $2_object_Ownership_$memory: $Memory $2_object_Ownership;

// struct object::UID at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:47:5+44
type {:datatype} $2_object_UID;
function {:constructor} $2_object_UID($id: $2_object_ID): $2_object_UID;
function {:inline} $Update'$2_object_UID'_id(s: $2_object_UID, x: $2_object_ID): $2_object_UID {
    $2_object_UID(x)
}
function $IsValid'$2_object_UID'(s: $2_object_UID): bool {
    $IsValid'$2_object_ID'($id#$2_object_UID(s))
}
function {:inline} $IsEqual'$2_object_UID'(s1: $2_object_UID, s2: $2_object_UID): bool {
    s1 == s2
}

// fun object::delete [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:127:5+104
procedure {:inline 1} $2_object_delete(_$t0: $2_object_UID) returns ()
{
    // declare local variables
    var $t1: $2_object_ID;
    var $t2: int;
    var $t0: $2_object_UID;
    var $temp_0'$2_object_UID': $2_object_UID;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[id]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:127:5+1
    assume {:print "$at(55,4459,4460)"} true;
    assume {:print "$track_local(8,11,0):", $t0} $t0 == $t0;

    // $t1 := unpack object::UID($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:128:13+24
    assume {:print "$at(55,4500,4524)"} true;
    $t1 := $id#$2_object_UID($t0);

    // $t2 := unpack object::ID($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:128:23+12
    $t2 := $bytes#$2_object_ID($t1);

    // opaque begin: object::delete_impl($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:129:9+18
    assume {:print "$at(55,4539,4557)"} true;

    // assume Not(exists<object::Ownership>($t2)) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:129:9+18
    assume !$ResourceExists($2_object_Ownership_$memory, $t2);

    // opaque end: object::delete_impl($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:129:9+18

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:130:5+1
    assume {:print "$at(55,4562,4563)"} true;
L1:

    // return () at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:130:5+1
    assume {:print "$at(55,4562,4563)"} true;
    return;

}

// fun object::new [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:116:5+141
procedure {:inline 1} $2_object_new(_$t0: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $2_object_UID, $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: $2_object_ID;
    var $t4: $2_object_UID;
    var $t0: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_object_UID': $2_object_UID;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[ctx]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:116:5+1
    assume {:print "$at(55,3956,3957)"} true;
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(8,10,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t1 := tx_context::fresh_object_address($t0) on_abort goto L2 with $t2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:118:29+37
    assume {:print "$at(55,4041,4078)"} true;
    call $t1,$t0 := $2_tx_context_fresh_object_address($t0);
    if ($abort_flag) {
        assume {:print "$at(55,4041,4078)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(8,10):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := pack object::ID($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:118:17+51
    $t3 := $2_object_ID($t1);

    // $t4 := pack object::UID($t3) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:117:9+84
    assume {:print "$at(55,4007,4091)"} true;
    $t4 := $2_object_UID($t3);

    // trace_return[0]($t4) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:117:9+84
    assume {:print "$track_return(8,10,0):", $t4} $t4 == $t4;

    // trace_local[ctx]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:117:9+84
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(8,10,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:120:5+1
    assume {:print "$at(55,4096,4097)"} true;
L1:

    // return $t4 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:120:5+1
    assume {:print "$at(55,4096,4097)"} true;
    $ret0 := $t4;
    $ret1 := $t0;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:120:5+1
L2:

    // abort($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:120:5+1
    assume {:print "$at(55,4096,4097)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun object::uid_to_bytes [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:103:5+91
procedure {:inline 1} $2_object_uid_to_bytes(_$t0: $2_object_UID) returns ($ret0: Vec (int))
{
    // declare local variables
    var $t1: $2_object_ID;
    var $t2: int;
    var $t3: Vec (int);
    var $t4: int;
    var $t0: $2_object_UID;
    var $temp_0'$2_object_UID': $2_object_UID;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[uid]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:103:5+1
    assume {:print "$at(55,3570,3571)"} true;
    assume {:print "$track_local(8,8,0):", $t0} $t0 == $t0;

    // $t1 := get_field<object::UID>.id($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:104:24+6
    assume {:print "$at(55,3642,3648)"} true;
    $t1 := $id#$2_object_UID($t0);

    // $t2 := get_field<object::ID>.bytes($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:104:23+13
    $t2 := $bytes#$2_object_ID($t1);

    // $t3 := bcs::to_bytes<address>($t2) on_abort goto L2 with $t4 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:104:9+28
    call $t3 := $1_bcs_to_bytes'address'($t2);
    if ($abort_flag) {
        assume {:print "$at(55,3627,3655)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(8,8):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t3) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:104:9+28
    assume {:print "$track_return(8,8,0):", $t3} $t3 == $t3;

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:105:5+1
    assume {:print "$at(55,3660,3661)"} true;
L1:

    // return $t3 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:105:5+1
    assume {:print "$at(55,3660,3661)"} true;
    $ret0 := $t3;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:105:5+1
L2:

    // abort($t4) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/object.move:105:5+1
    assume {:print "$at(55,3660,3661)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// spec fun at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/prover.move:14:10+180
function {:inline} $2_prover_owned'$0_vault_Vault'#0_#1''($2_object_Ownership_$memory: $Memory $2_object_Ownership, obj: $0_vault_Vault'#0_#1'): bool {
    (var addr := $bytes#$2_object_ID($2_object_$id'$0_vault_Vault'#0_#1''(obj)); ($ResourceExists($2_object_Ownership_$memory, addr) && $IsEqual'u64'($status#$2_object_Ownership($ResourceValue($2_object_Ownership_$memory, addr)), 1)))
}

// fun transfer::public_share_object<vault::Vault<#0, #1>> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:69:5+93
procedure {:inline 1} $2_transfer_public_share_object'$0_vault_Vault'#0_#1''(_$t0: $0_vault_Vault'#0_#1') returns ()
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t0: $0_vault_Vault'#0_#1';
    var $temp_0'$0_vault_Vault'#0_#1'': $0_vault_Vault'#0_#1';
    var $temp_0'$2_object_Ownership': $2_object_Ownership;
    var $temp_0'bool': bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[obj]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:69:5+1
    assume {:print "$at(68,3573,3574)"} true;
    assume {:print "$track_local(10,5,0):", $t0} $t0 == $t0;

    // opaque begin: transfer::share_object_impl<#0>($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:70:9+22
    assume {:print "$at(68,3638,3660)"} true;

    // assume Identical($t1, prover::owned<#0>($t0)) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:70:9+22
    assume ($t1 == $2_prover_owned'$0_vault_Vault'#0_#1''($2_object_Ownership_$memory, $t0));

    // if ($t1) goto L4 else goto L3 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:70:9+22
    if ($t1) { goto L4; } else { goto L3; }

    // label L4 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:70:9+22
L4:

    // trace_abort($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:70:9+22
    assume {:print "$at(68,3638,3660)"} true;
    assume {:print "$track_abort(10,5):", $t2} $t2 == $t2;

    // goto L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:70:9+22
    goto L2;

    // label L3 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:70:9+22
L3:

    // modifies global<object::Ownership>(select object::ID.bytes(object::$id<#0>($t0))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:70:9+22
    assume {:print "$at(68,3638,3660)"} true;
    havoc $temp_0'bool';
    if ($temp_0'bool') {
        havoc $temp_0'$2_object_Ownership';
        $2_object_Ownership_$memory := $ResourceUpdate($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$0_vault_Vault'#0_#1''($t0)), $temp_0'$2_object_Ownership');
    } else {
        $2_object_Ownership_$memory := $ResourceRemove($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$0_vault_Vault'#0_#1''($t0)));
    }

    // assume exists<object::Ownership>(select object::ID.bytes(object::$id<#0>($t0))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:70:9+22
    assume $ResourceExists($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$0_vault_Vault'#0_#1''($t0)));

    // assume Eq<u64>(select object::Ownership.status(global<object::Ownership>(select object::ID.bytes(object::$id<#0>($t0)))), 2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:70:9+22
    assume $IsEqual'u64'($status#$2_object_Ownership($ResourceValue($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$0_vault_Vault'#0_#1''($t0)))), 2);

    // opaque end: transfer::share_object_impl<#0>($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:70:9+22

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:71:5+1
    assume {:print "$at(68,3665,3666)"} true;
L1:

    // return () at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:71:5+1
    assume {:print "$at(68,3665,3666)"} true;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:71:5+1
L2:

    // abort($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:71:5+1
    assume {:print "$at(68,3665,3666)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun transfer::public_transfer<coin::Coin<#0>> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:33:5+116
procedure {:inline 1} $2_transfer_public_transfer'$2_coin_Coin'#0''(_$t0: $2_coin_Coin'#0', _$t1: int) returns ()
{
    // declare local variables
    var $t0: $2_coin_Coin'#0';
    var $t1: int;
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'$2_object_Ownership': $2_object_Ownership;
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[obj]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:33:5+1
    assume {:print "$at(68,1569,1570)"} true;
    assume {:print "$track_local(10,1,0):", $t0} $t0 == $t0;

    // trace_local[recipient]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:33:5+1
    assume {:print "$track_local(10,1,1):", $t1} $t1 == $t1;

    // opaque begin: transfer::transfer_impl<#0>($t0, $t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:34:9+29
    assume {:print "$at(68,1650,1679)"} true;

    // modifies global<object::Ownership>(select object::ID.bytes(object::$id<#0>($t0))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:34:9+29
    havoc $temp_0'bool';
    if ($temp_0'bool') {
        havoc $temp_0'$2_object_Ownership';
        $2_object_Ownership_$memory := $ResourceUpdate($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$2_coin_Coin'#0''($t0)), $temp_0'$2_object_Ownership');
    } else {
        $2_object_Ownership_$memory := $ResourceRemove($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$2_coin_Coin'#0''($t0)));
    }

    // assume exists<object::Ownership>(select object::ID.bytes(object::$id<#0>($t0))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:34:9+29
    assume $ResourceExists($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$2_coin_Coin'#0''($t0)));

    // assume Eq<address>(select object::Ownership.owner(global<object::Ownership>(select object::ID.bytes(object::$id<#0>($t0)))), $t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:34:9+29
    assume $IsEqual'address'($owner#$2_object_Ownership($ResourceValue($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$2_coin_Coin'#0''($t0)))), $t1);

    // assume Eq<u64>(select object::Ownership.status(global<object::Ownership>(select object::ID.bytes(object::$id<#0>($t0)))), 1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:34:9+29
    assume $IsEqual'u64'($status#$2_object_Ownership($ResourceValue($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$2_coin_Coin'#0''($t0)))), 1);

    // opaque end: transfer::transfer_impl<#0>($t0, $t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:34:9+29

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:35:5+1
    assume {:print "$at(68,1684,1685)"} true;
L1:

    // return () at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:35:5+1
    assume {:print "$at(68,1684,1685)"} true;
    return;

}

// fun transfer::public_transfer<coin::Coin<#1>> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:33:5+116
procedure {:inline 1} $2_transfer_public_transfer'$2_coin_Coin'#1''(_$t0: $2_coin_Coin'#1', _$t1: int) returns ()
{
    // declare local variables
    var $t0: $2_coin_Coin'#1';
    var $t1: int;
    var $temp_0'$2_coin_Coin'#1'': $2_coin_Coin'#1';
    var $temp_0'$2_object_Ownership': $2_object_Ownership;
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[obj]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:33:5+1
    assume {:print "$at(68,1569,1570)"} true;
    assume {:print "$track_local(10,1,0):", $t0} $t0 == $t0;

    // trace_local[recipient]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:33:5+1
    assume {:print "$track_local(10,1,1):", $t1} $t1 == $t1;

    // opaque begin: transfer::transfer_impl<#0>($t0, $t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:34:9+29
    assume {:print "$at(68,1650,1679)"} true;

    // modifies global<object::Ownership>(select object::ID.bytes(object::$id<#0>($t0))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:34:9+29
    havoc $temp_0'bool';
    if ($temp_0'bool') {
        havoc $temp_0'$2_object_Ownership';
        $2_object_Ownership_$memory := $ResourceUpdate($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$2_coin_Coin'#1''($t0)), $temp_0'$2_object_Ownership');
    } else {
        $2_object_Ownership_$memory := $ResourceRemove($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$2_coin_Coin'#1''($t0)));
    }

    // assume exists<object::Ownership>(select object::ID.bytes(object::$id<#0>($t0))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:34:9+29
    assume $ResourceExists($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$2_coin_Coin'#1''($t0)));

    // assume Eq<address>(select object::Ownership.owner(global<object::Ownership>(select object::ID.bytes(object::$id<#0>($t0)))), $t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:34:9+29
    assume $IsEqual'address'($owner#$2_object_Ownership($ResourceValue($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$2_coin_Coin'#1''($t0)))), $t1);

    // assume Eq<u64>(select object::Ownership.status(global<object::Ownership>(select object::ID.bytes(object::$id<#0>($t0)))), 1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:34:9+29
    assume $IsEqual'u64'($status#$2_object_Ownership($ResourceValue($2_object_Ownership_$memory, $bytes#$2_object_ID($2_object_$id'$2_coin_Coin'#1''($t0)))), 1);

    // opaque end: transfer::transfer_impl<#0>($t0, $t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:34:9+29

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:35:5+1
    assume {:print "$at(68,1684,1685)"} true;
L1:

    // return () at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/transfer.move:35:5+1
    assume {:print "$at(68,1684,1685)"} true;
    return;

}

// struct balance::Balance<#0> at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:32:5+62
type {:datatype} $2_balance_Balance'#0';
function {:constructor} $2_balance_Balance'#0'($value: int): $2_balance_Balance'#0';
function {:inline} $Update'$2_balance_Balance'#0''_value(s: $2_balance_Balance'#0', x: int): $2_balance_Balance'#0' {
    $2_balance_Balance'#0'(x)
}
function $IsValid'$2_balance_Balance'#0''(s: $2_balance_Balance'#0'): bool {
    $IsValid'u64'($value#$2_balance_Balance'#0'(s))
}
function {:inline} $IsEqual'$2_balance_Balance'#0''(s1: $2_balance_Balance'#0', s2: $2_balance_Balance'#0'): bool {
    s1 == s2
}

// struct balance::Balance<#1> at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:32:5+62
type {:datatype} $2_balance_Balance'#1';
function {:constructor} $2_balance_Balance'#1'($value: int): $2_balance_Balance'#1';
function {:inline} $Update'$2_balance_Balance'#1''_value(s: $2_balance_Balance'#1', x: int): $2_balance_Balance'#1' {
    $2_balance_Balance'#1'(x)
}
function $IsValid'$2_balance_Balance'#1''(s: $2_balance_Balance'#1'): bool {
    $IsValid'u64'($value#$2_balance_Balance'#1'(s))
}
function {:inline} $IsEqual'$2_balance_Balance'#1''(s1: $2_balance_Balance'#1', s2: $2_balance_Balance'#1'): bool {
    s1 == s2
}

// fun balance::value<#0> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:37:5+70
procedure {:inline 1} $2_balance_value'#0'(_$t0: $2_balance_Balance'#0') returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t0: $2_balance_Balance'#0';
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:37:5+1
    assume {:print "$at(25,1128,1129)"} true;
    assume {:print "$track_local(14,0,0):", $t0} $t0 == $t0;

    // $t1 := get_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:38:9+10
    assume {:print "$at(25,1182,1192)"} true;
    $t1 := $value#$2_balance_Balance'#0'($t0);

    // trace_return[0]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:38:9+10
    assume {:print "$track_return(14,0,0):", $t1} $t1 == $t1;

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:39:5+1
    assume {:print "$at(25,1197,1198)"} true;
L1:

    // return $t1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:39:5+1
    assume {:print "$at(25,1197,1198)"} true;
    $ret0 := $t1;
    return;

}

// fun balance::value<#1> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:37:5+70
procedure {:inline 1} $2_balance_value'#1'(_$t0: $2_balance_Balance'#1') returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t0: $2_balance_Balance'#1';
    var $temp_0'$2_balance_Balance'#1'': $2_balance_Balance'#1';
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:37:5+1
    assume {:print "$at(25,1128,1129)"} true;
    assume {:print "$track_local(14,0,0):", $t0} $t0 == $t0;

    // $t1 := get_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:38:9+10
    assume {:print "$at(25,1182,1192)"} true;
    $t1 := $value#$2_balance_Balance'#1'($t0);

    // trace_return[0]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:38:9+10
    assume {:print "$track_return(14,0,0):", $t1} $t1 == $t1;

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:39:5+1
    assume {:print "$at(25,1197,1198)"} true;
L1:

    // return $t1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:39:5+1
    assume {:print "$at(25,1197,1198)"} true;
    $ret0 := $t1;
    return;

}

// fun balance::join<#0> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:77:5+176
procedure {:inline 1} $2_balance_join'#0'(_$t0: $Mutation ($2_balance_Balance'#0'), _$t1: $2_balance_Balance'#0') returns ($ret0: int, $ret1: $Mutation ($2_balance_Balance'#0'))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation (int);
    var $t8: int;
    var $t0: $Mutation ($2_balance_Balance'#0');
    var $t1: $2_balance_Balance'#0';
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:77:5+1
    assume {:print "$at(25,2294,2295)"} true;
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(14,6,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // trace_local[balance]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:77:5+1
    assume {:print "$track_local(14,6,1):", $t1} $t1 == $t1;

    // $t3 := unpack balance::Balance<#0>($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:78:13+17
    assume {:print "$at(25,2376,2393)"} true;
    $t3 := $value#$2_balance_Balance'#0'($t1);

    // trace_local[value#1#0]($t3) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:78:23+5
    assume {:print "$track_local(14,6,2):", $t3} $t3 == $t3;

    // $t4 := get_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:79:22+10
    assume {:print "$at(25,2426,2436)"} true;
    $t4 := $value#$2_balance_Balance'#0'($Dereference($t0));

    // $t5 := +($t4, $t3) on_abort goto L2 with $t6 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:79:33+1
    call $t5 := $Addu256($t4, $t3);
    if ($abort_flag) {
        assume {:print "$at(25,2437,2438)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(14,6):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t7 := borrow_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:79:9+10
    $t7 := $ChildMutation($t0, 0, $value#$2_balance_Balance'#0'($Dereference($t0)));

    // write_ref($t7, $t5) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:79:9+31
    $t7 := $UpdateMutation($t7, $t5);

    // write_back[Reference($t0).value (u64)]($t7) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:79:9+31
    $t0 := $UpdateMutation($t0, $Update'$2_balance_Balance'#0''_value($Dereference($t0), $Dereference($t7)));

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:79:9+31
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(14,6,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // $t8 := get_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:80:9+10
    assume {:print "$at(25,2454,2464)"} true;
    $t8 := $value#$2_balance_Balance'#0'($Dereference($t0));

    // trace_return[0]($t8) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:80:9+10
    assume {:print "$track_return(14,6,0):", $t8} $t8 == $t8;

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:80:9+10
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(14,6,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:81:5+1
    assume {:print "$at(25,2469,2470)"} true;
L1:

    // return $t8 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:81:5+1
    assume {:print "$at(25,2469,2470)"} true;
    $ret0 := $t8;
    $ret1 := $t0;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:81:5+1
L2:

    // abort($t6) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:81:5+1
    assume {:print "$at(25,2469,2470)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun balance::join<#1> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:77:5+176
procedure {:inline 1} $2_balance_join'#1'(_$t0: $Mutation ($2_balance_Balance'#1'), _$t1: $2_balance_Balance'#1') returns ($ret0: int, $ret1: $Mutation ($2_balance_Balance'#1'))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation (int);
    var $t8: int;
    var $t0: $Mutation ($2_balance_Balance'#1');
    var $t1: $2_balance_Balance'#1';
    var $temp_0'$2_balance_Balance'#1'': $2_balance_Balance'#1';
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:77:5+1
    assume {:print "$at(25,2294,2295)"} true;
    $temp_0'$2_balance_Balance'#1'' := $Dereference($t0);
    assume {:print "$track_local(14,6,0):", $temp_0'$2_balance_Balance'#1''} $temp_0'$2_balance_Balance'#1'' == $temp_0'$2_balance_Balance'#1'';

    // trace_local[balance]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:77:5+1
    assume {:print "$track_local(14,6,1):", $t1} $t1 == $t1;

    // $t3 := unpack balance::Balance<#0>($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:78:13+17
    assume {:print "$at(25,2376,2393)"} true;
    $t3 := $value#$2_balance_Balance'#1'($t1);

    // trace_local[value#1#0]($t3) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:78:23+5
    assume {:print "$track_local(14,6,2):", $t3} $t3 == $t3;

    // $t4 := get_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:79:22+10
    assume {:print "$at(25,2426,2436)"} true;
    $t4 := $value#$2_balance_Balance'#1'($Dereference($t0));

    // $t5 := +($t4, $t3) on_abort goto L2 with $t6 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:79:33+1
    call $t5 := $Addu256($t4, $t3);
    if ($abort_flag) {
        assume {:print "$at(25,2437,2438)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(14,6):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t7 := borrow_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:79:9+10
    $t7 := $ChildMutation($t0, 0, $value#$2_balance_Balance'#1'($Dereference($t0)));

    // write_ref($t7, $t5) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:79:9+31
    $t7 := $UpdateMutation($t7, $t5);

    // write_back[Reference($t0).value (u64)]($t7) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:79:9+31
    $t0 := $UpdateMutation($t0, $Update'$2_balance_Balance'#1''_value($Dereference($t0), $Dereference($t7)));

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:79:9+31
    $temp_0'$2_balance_Balance'#1'' := $Dereference($t0);
    assume {:print "$track_local(14,6,0):", $temp_0'$2_balance_Balance'#1''} $temp_0'$2_balance_Balance'#1'' == $temp_0'$2_balance_Balance'#1'';

    // $t8 := get_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:80:9+10
    assume {:print "$at(25,2454,2464)"} true;
    $t8 := $value#$2_balance_Balance'#1'($Dereference($t0));

    // trace_return[0]($t8) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:80:9+10
    assume {:print "$track_return(14,6,0):", $t8} $t8 == $t8;

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:80:9+10
    $temp_0'$2_balance_Balance'#1'' := $Dereference($t0);
    assume {:print "$track_local(14,6,0):", $temp_0'$2_balance_Balance'#1''} $temp_0'$2_balance_Balance'#1'' == $temp_0'$2_balance_Balance'#1'';

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:81:5+1
    assume {:print "$at(25,2469,2470)"} true;
L1:

    // return $t8 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:81:5+1
    assume {:print "$at(25,2469,2470)"} true;
    $ret0 := $t8;
    $ret1 := $t0;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:81:5+1
L2:

    // abort($t6) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:81:5+1
    assume {:print "$at(25,2469,2470)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun balance::split<#0> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:89:5+191
procedure {:inline 1} $2_balance_split'#0'(_$t0: $Mutation ($2_balance_Balance'#0'), _$t1: int) returns ($ret0: $2_balance_Balance'#0', $ret1: $Mutation ($2_balance_Balance'#0'))
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $Mutation (int);
    var $t9: $2_balance_Balance'#0';
    var $t0: $Mutation ($2_balance_Balance'#0');
    var $t1: int;
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:89:5+1
    assume {:print "$at(25,2658,2659)"} true;
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(14,7,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // trace_local[value]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:89:5+1
    assume {:print "$track_local(14,7,1):", $t1} $t1 == $t1;

    // $t2 := get_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:17+10
    assume {:print "$at(25,2743,2753)"} true;
    $t2 := $value#$2_balance_Balance'#0'($Dereference($t0));

    // $t3 := >=($t2, $t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:28+2
    call $t3 := $Ge($t2, $t1);

    // if ($t3) goto L1 else goto L0 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
L1:

    // goto L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
    assume {:print "$at(25,2735,2775)"} true;
    goto L2;

    // label L0 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
L0:

    // destroy($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
    assume {:print "$at(25,2735,2775)"} true;

    // $t4 := 2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:38+10
    $t4 := 2;
    assume $IsValid'u64'($t4);

    // trace_abort($t4) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
    assume {:print "$at(25,2735,2775)"} true;
    assume {:print "$track_abort(14,7):", $t4} $t4 == $t4;

    // $t5 := move($t4) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
    $t5 := $t4;

    // goto L4 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
    goto L4;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:22+4
    assume {:print "$at(25,2798,2802)"} true;
L2:

    // $t6 := get_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:22+10
    assume {:print "$at(25,2798,2808)"} true;
    $t6 := $value#$2_balance_Balance'#0'($Dereference($t0));

    // $t7 := -($t6, $t1) on_abort goto L4 with $t5 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:33+1
    call $t7 := $Sub($t6, $t1);
    if ($abort_flag) {
        assume {:print "$at(25,2809,2810)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(14,7):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t8 := borrow_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:9+10
    $t8 := $ChildMutation($t0, 0, $value#$2_balance_Balance'#0'($Dereference($t0)));

    // write_ref($t8, $t7) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:9+31
    $t8 := $UpdateMutation($t8, $t7);

    // write_back[Reference($t0).value (u64)]($t8) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:9+31
    $t0 := $UpdateMutation($t0, $Update'$2_balance_Balance'#0''_value($Dereference($t0), $Dereference($t8)));

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:9+31
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(14,7,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // $t9 := pack balance::Balance<#0>($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:92:9+17
    assume {:print "$at(25,2826,2843)"} true;
    $t9 := $2_balance_Balance'#0'($t1);

    // trace_return[0]($t9) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:92:9+17
    assume {:print "$track_return(14,7,0):", $t9} $t9 == $t9;

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:92:9+17
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(14,7,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // label L3 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:93:5+1
    assume {:print "$at(25,2848,2849)"} true;
L3:

    // return $t9 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:93:5+1
    assume {:print "$at(25,2848,2849)"} true;
    $ret0 := $t9;
    $ret1 := $t0;
    return;

    // label L4 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:93:5+1
L4:

    // abort($t5) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:93:5+1
    assume {:print "$at(25,2848,2849)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun balance::split<#1> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:89:5+191
procedure {:inline 1} $2_balance_split'#1'(_$t0: $Mutation ($2_balance_Balance'#1'), _$t1: int) returns ($ret0: $2_balance_Balance'#1', $ret1: $Mutation ($2_balance_Balance'#1'))
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $Mutation (int);
    var $t9: $2_balance_Balance'#1';
    var $t0: $Mutation ($2_balance_Balance'#1');
    var $t1: int;
    var $temp_0'$2_balance_Balance'#1'': $2_balance_Balance'#1';
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:89:5+1
    assume {:print "$at(25,2658,2659)"} true;
    $temp_0'$2_balance_Balance'#1'' := $Dereference($t0);
    assume {:print "$track_local(14,7,0):", $temp_0'$2_balance_Balance'#1''} $temp_0'$2_balance_Balance'#1'' == $temp_0'$2_balance_Balance'#1'';

    // trace_local[value]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:89:5+1
    assume {:print "$track_local(14,7,1):", $t1} $t1 == $t1;

    // $t2 := get_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:17+10
    assume {:print "$at(25,2743,2753)"} true;
    $t2 := $value#$2_balance_Balance'#1'($Dereference($t0));

    // $t3 := >=($t2, $t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:28+2
    call $t3 := $Ge($t2, $t1);

    // if ($t3) goto L1 else goto L0 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
L1:

    // goto L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
    assume {:print "$at(25,2735,2775)"} true;
    goto L2;

    // label L0 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
L0:

    // destroy($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
    assume {:print "$at(25,2735,2775)"} true;

    // $t4 := 2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:38+10
    $t4 := 2;
    assume $IsValid'u64'($t4);

    // trace_abort($t4) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
    assume {:print "$at(25,2735,2775)"} true;
    assume {:print "$track_abort(14,7):", $t4} $t4 == $t4;

    // $t5 := move($t4) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
    $t5 := $t4;

    // goto L4 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:90:9+40
    goto L4;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:22+4
    assume {:print "$at(25,2798,2802)"} true;
L2:

    // $t6 := get_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:22+10
    assume {:print "$at(25,2798,2808)"} true;
    $t6 := $value#$2_balance_Balance'#1'($Dereference($t0));

    // $t7 := -($t6, $t1) on_abort goto L4 with $t5 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:33+1
    call $t7 := $Sub($t6, $t1);
    if ($abort_flag) {
        assume {:print "$at(25,2809,2810)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(14,7):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t8 := borrow_field<balance::Balance<#0>>.value($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:9+10
    $t8 := $ChildMutation($t0, 0, $value#$2_balance_Balance'#1'($Dereference($t0)));

    // write_ref($t8, $t7) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:9+31
    $t8 := $UpdateMutation($t8, $t7);

    // write_back[Reference($t0).value (u64)]($t8) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:9+31
    $t0 := $UpdateMutation($t0, $Update'$2_balance_Balance'#1''_value($Dereference($t0), $Dereference($t8)));

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:91:9+31
    $temp_0'$2_balance_Balance'#1'' := $Dereference($t0);
    assume {:print "$track_local(14,7,0):", $temp_0'$2_balance_Balance'#1''} $temp_0'$2_balance_Balance'#1'' == $temp_0'$2_balance_Balance'#1'';

    // $t9 := pack balance::Balance<#0>($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:92:9+17
    assume {:print "$at(25,2826,2843)"} true;
    $t9 := $2_balance_Balance'#1'($t1);

    // trace_return[0]($t9) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:92:9+17
    assume {:print "$track_return(14,7,0):", $t9} $t9 == $t9;

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:92:9+17
    $temp_0'$2_balance_Balance'#1'' := $Dereference($t0);
    assume {:print "$track_local(14,7,0):", $temp_0'$2_balance_Balance'#1''} $temp_0'$2_balance_Balance'#1'' == $temp_0'$2_balance_Balance'#1'';

    // label L3 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:93:5+1
    assume {:print "$at(25,2848,2849)"} true;
L3:

    // return $t9 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:93:5+1
    assume {:print "$at(25,2848,2849)"} true;
    $ret0 := $t9;
    $ret1 := $t0;
    return;

    // label L4 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:93:5+1
L4:

    // abort($t5) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:93:5+1
    assume {:print "$at(25,2848,2849)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun balance::zero<#0> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:67:5+69
procedure {:inline 1} $2_balance_zero'#0'() returns ($ret0: $2_balance_Balance'#0')
{
    // declare local variables
    var $t0: int;
    var $t1: $2_balance_Balance'#0';
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';

    // bytecode translation starts here
    // $t0 := 0 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:68:26+1
    assume {:print "$at(25,2160,2161)"} true;
    $t0 := 0;
    assume $IsValid'u64'($t0);

    // $t1 := pack balance::Balance<#0>($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:68:9+20
    $t1 := $2_balance_Balance'#0'($t0);

    // trace_return[0]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:68:9+20
    assume {:print "$track_return(14,5,0):", $t1} $t1 == $t1;

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:69:5+1
    assume {:print "$at(25,2168,2169)"} true;
L1:

    // return $t1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/balance.move:69:5+1
    assume {:print "$at(25,2168,2169)"} true;
    $ret0 := $t1;
    return;

}

// struct coin::Coin<#0> at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:27:5+90
type {:datatype} $2_coin_Coin'#0';
function {:constructor} $2_coin_Coin'#0'($id: $2_object_UID, $balance: $2_balance_Balance'#0'): $2_coin_Coin'#0';
function {:inline} $Update'$2_coin_Coin'#0''_id(s: $2_coin_Coin'#0', x: $2_object_UID): $2_coin_Coin'#0' {
    $2_coin_Coin'#0'(x, $balance#$2_coin_Coin'#0'(s))
}
function {:inline} $Update'$2_coin_Coin'#0''_balance(s: $2_coin_Coin'#0', x: $2_balance_Balance'#0'): $2_coin_Coin'#0' {
    $2_coin_Coin'#0'($id#$2_coin_Coin'#0'(s), x)
}
function $IsValid'$2_coin_Coin'#0''(s: $2_coin_Coin'#0'): bool {
    $IsValid'$2_object_UID'($id#$2_coin_Coin'#0'(s))
      && $IsValid'$2_balance_Balance'#0''($balance#$2_coin_Coin'#0'(s))
}
function {:inline} $IsEqual'$2_coin_Coin'#0''(s1: $2_coin_Coin'#0', s2: $2_coin_Coin'#0'): bool {
    s1 == s2
}
var $2_coin_Coin'#0'_$memory: $Memory $2_coin_Coin'#0';

// struct coin::Coin<#1> at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:27:5+90
type {:datatype} $2_coin_Coin'#1';
function {:constructor} $2_coin_Coin'#1'($id: $2_object_UID, $balance: $2_balance_Balance'#1'): $2_coin_Coin'#1';
function {:inline} $Update'$2_coin_Coin'#1''_id(s: $2_coin_Coin'#1', x: $2_object_UID): $2_coin_Coin'#1' {
    $2_coin_Coin'#1'(x, $balance#$2_coin_Coin'#1'(s))
}
function {:inline} $Update'$2_coin_Coin'#1''_balance(s: $2_coin_Coin'#1', x: $2_balance_Balance'#1'): $2_coin_Coin'#1' {
    $2_coin_Coin'#1'($id#$2_coin_Coin'#1'(s), x)
}
function $IsValid'$2_coin_Coin'#1''(s: $2_coin_Coin'#1'): bool {
    $IsValid'$2_object_UID'($id#$2_coin_Coin'#1'(s))
      && $IsValid'$2_balance_Balance'#1''($balance#$2_coin_Coin'#1'(s))
}
function {:inline} $IsEqual'$2_coin_Coin'#1''(s1: $2_coin_Coin'#1', s2: $2_coin_Coin'#1'): bool {
    s1 == s2
}
var $2_coin_Coin'#1'_$memory: $Memory $2_coin_Coin'#1';

// fun coin::value<#0> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:101:5+86
procedure {:inline 1} $2_coin_value'#0'(_$t0: $2_coin_Coin'#0') returns ($ret0: int)
{
    // declare local variables
    var $t1: $2_balance_Balance'#0';
    var $t2: int;
    var $t3: int;
    var $t0: $2_coin_Coin'#0';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:101:5+1
    assume {:print "$at(29,3692,3693)"} true;
    assume {:print "$track_local(15,4,0):", $t0} $t0 == $t0;

    // $t1 := get_field<coin::Coin<#0>>.balance($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:102:24+13
    assume {:print "$at(29,3758,3771)"} true;
    $t1 := $balance#$2_coin_Coin'#0'($t0);

    // $t2 := balance::value<#0>($t1) on_abort goto L2 with $t3 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:102:9+29
    call $t2 := $2_balance_value'#0'($t1);
    if ($abort_flag) {
        assume {:print "$at(29,3743,3772)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(15,4):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:102:9+29
    assume {:print "$track_return(15,4,0):", $t2} $t2 == $t2;

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:103:5+1
    assume {:print "$at(29,3777,3778)"} true;
L1:

    // return $t2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:103:5+1
    assume {:print "$at(29,3777,3778)"} true;
    $ret0 := $t2;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:103:5+1
L2:

    // abort($t3) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:103:5+1
    assume {:print "$at(29,3777,3778)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun coin::value<#1> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:101:5+86
procedure {:inline 1} $2_coin_value'#1'(_$t0: $2_coin_Coin'#1') returns ($ret0: int)
{
    // declare local variables
    var $t1: $2_balance_Balance'#1';
    var $t2: int;
    var $t3: int;
    var $t0: $2_coin_Coin'#1';
    var $temp_0'$2_coin_Coin'#1'': $2_coin_Coin'#1';
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:101:5+1
    assume {:print "$at(29,3692,3693)"} true;
    assume {:print "$track_local(15,4,0):", $t0} $t0 == $t0;

    // $t1 := get_field<coin::Coin<#0>>.balance($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:102:24+13
    assume {:print "$at(29,3758,3771)"} true;
    $t1 := $balance#$2_coin_Coin'#1'($t0);

    // $t2 := balance::value<#0>($t1) on_abort goto L2 with $t3 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:102:9+29
    call $t2 := $2_balance_value'#1'($t1);
    if ($abort_flag) {
        assume {:print "$at(29,3743,3772)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(15,4):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:102:9+29
    assume {:print "$track_return(15,4,0):", $t2} $t2 == $t2;

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:103:5+1
    assume {:print "$at(29,3777,3778)"} true;
L1:

    // return $t2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:103:5+1
    assume {:print "$at(29,3777,3778)"} true;
    $ret0 := $t2;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:103:5+1
L2:

    // abort($t3) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:103:5+1
    assume {:print "$at(29,3777,3778)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun coin::join<#0> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:164:5+181
procedure {:inline 1} $2_coin_join'#0'(_$t0: $Mutation ($2_coin_Coin'#0'), _$t1: $2_coin_Coin'#0') returns ($ret0: $Mutation ($2_coin_Coin'#0'))
{
    // declare local variables
    var $t2: $2_balance_Balance'#0';
    var $t3: int;
    var $t4: $2_object_UID;
    var $t5: $2_balance_Balance'#0';
    var $t6: int;
    var $t7: $Mutation ($2_balance_Balance'#0');
    var $t8: int;
    var $t0: $Mutation ($2_coin_Coin'#0');
    var $t1: $2_coin_Coin'#0';
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t3, select balance::Balance.value(select coin::Coin.balance($t0))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:171:9+36
    assume {:print "$at(29,5814,5850)"} true;
    assume ($t3 == $value#$2_balance_Balance'#0'($balance#$2_coin_Coin'#0'($Dereference($t0))));

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:164:5+1
    assume {:print "$at(29,5607,5608)"} true;
    $temp_0'$2_coin_Coin'#0'' := $Dereference($t0);
    assume {:print "$track_local(15,11,0):", $temp_0'$2_coin_Coin'#0''} $temp_0'$2_coin_Coin'#0'' == $temp_0'$2_coin_Coin'#0'';

    // trace_local[c]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:164:5+1
    assume {:print "$track_local(15,11,1):", $t1} $t1 == $t1;

    // ($t4, $t5) := unpack coin::Coin<#0>($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:165:13+20
    assume {:print "$at(29,5678,5698)"} true;
    $t4 := $id#$2_coin_Coin'#0'($t1);
    $t5 := $balance#$2_coin_Coin'#0'($t1);

    // trace_local[balance#1#0]($t5) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:165:24+7
    assume {:print "$track_local(15,11,2):", $t5} $t5 == $t5;

    // object::delete($t4) on_abort goto L2 with $t6 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:166:9+18
    assume {:print "$at(29,5712,5730)"} true;
    call $2_object_delete($t4);
    if ($abort_flag) {
        assume {:print "$at(29,5712,5730)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,11):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t7 := borrow_field<coin::Coin<#0>>.balance($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:167:23+17
    assume {:print "$at(29,5754,5771)"} true;
    $t7 := $ChildMutation($t0, 1, $balance#$2_coin_Coin'#0'($Dereference($t0)));

    // $t8 := balance::join<#0>($t7, $t5) on_abort goto L2 with $t6 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:167:9+41
    call $t8,$t7 := $2_balance_join'#0'($t7, $t5);
    if ($abort_flag) {
        assume {:print "$at(29,5740,5781)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,11):", $t6} $t6 == $t6;
        goto L2;
    }

    // write_back[Reference($t0).balance (balance::Balance<#0>)]($t7) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:167:9+41
    $t0 := $UpdateMutation($t0, $Update'$2_coin_Coin'#0''_balance($Dereference($t0), $Dereference($t7)));

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:167:9+41
    $temp_0'$2_coin_Coin'#0'' := $Dereference($t0);
    assume {:print "$track_local(15,11,0):", $temp_0'$2_coin_Coin'#0''} $temp_0'$2_coin_Coin'#0'' == $temp_0'$2_coin_Coin'#0'';

    // destroy($t8) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:167:9+41

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:167:50+1
    $temp_0'$2_coin_Coin'#0'' := $Dereference($t0);
    assume {:print "$track_local(15,11,0):", $temp_0'$2_coin_Coin'#0''} $temp_0'$2_coin_Coin'#0'' == $temp_0'$2_coin_Coin'#0'';

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:168:5+1
    assume {:print "$at(29,5787,5788)"} true;
L1:

    // return () at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:168:5+1
    assume {:print "$at(29,5787,5788)"} true;
    $ret0 := $t0;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:168:5+1
L2:

    // abort($t6) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:168:5+1
    assume {:print "$at(29,5787,5788)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun coin::join<#1> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:164:5+181
procedure {:inline 1} $2_coin_join'#1'(_$t0: $Mutation ($2_coin_Coin'#1'), _$t1: $2_coin_Coin'#1') returns ($ret0: $Mutation ($2_coin_Coin'#1'))
{
    // declare local variables
    var $t2: $2_balance_Balance'#1';
    var $t3: int;
    var $t4: $2_object_UID;
    var $t5: $2_balance_Balance'#1';
    var $t6: int;
    var $t7: $Mutation ($2_balance_Balance'#1');
    var $t8: int;
    var $t0: $Mutation ($2_coin_Coin'#1');
    var $t1: $2_coin_Coin'#1';
    var $temp_0'$2_balance_Balance'#1'': $2_balance_Balance'#1';
    var $temp_0'$2_coin_Coin'#1'': $2_coin_Coin'#1';
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t3, select balance::Balance.value(select coin::Coin.balance($t0))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:171:9+36
    assume {:print "$at(29,5814,5850)"} true;
    assume ($t3 == $value#$2_balance_Balance'#1'($balance#$2_coin_Coin'#1'($Dereference($t0))));

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:164:5+1
    assume {:print "$at(29,5607,5608)"} true;
    $temp_0'$2_coin_Coin'#1'' := $Dereference($t0);
    assume {:print "$track_local(15,11,0):", $temp_0'$2_coin_Coin'#1''} $temp_0'$2_coin_Coin'#1'' == $temp_0'$2_coin_Coin'#1'';

    // trace_local[c]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:164:5+1
    assume {:print "$track_local(15,11,1):", $t1} $t1 == $t1;

    // ($t4, $t5) := unpack coin::Coin<#0>($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:165:13+20
    assume {:print "$at(29,5678,5698)"} true;
    $t4 := $id#$2_coin_Coin'#1'($t1);
    $t5 := $balance#$2_coin_Coin'#1'($t1);

    // trace_local[balance#1#0]($t5) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:165:24+7
    assume {:print "$track_local(15,11,2):", $t5} $t5 == $t5;

    // object::delete($t4) on_abort goto L2 with $t6 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:166:9+18
    assume {:print "$at(29,5712,5730)"} true;
    call $2_object_delete($t4);
    if ($abort_flag) {
        assume {:print "$at(29,5712,5730)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,11):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t7 := borrow_field<coin::Coin<#0>>.balance($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:167:23+17
    assume {:print "$at(29,5754,5771)"} true;
    $t7 := $ChildMutation($t0, 1, $balance#$2_coin_Coin'#1'($Dereference($t0)));

    // $t8 := balance::join<#0>($t7, $t5) on_abort goto L2 with $t6 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:167:9+41
    call $t8,$t7 := $2_balance_join'#1'($t7, $t5);
    if ($abort_flag) {
        assume {:print "$at(29,5740,5781)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,11):", $t6} $t6 == $t6;
        goto L2;
    }

    // write_back[Reference($t0).balance (balance::Balance<#0>)]($t7) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:167:9+41
    $t0 := $UpdateMutation($t0, $Update'$2_coin_Coin'#1''_balance($Dereference($t0), $Dereference($t7)));

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:167:9+41
    $temp_0'$2_coin_Coin'#1'' := $Dereference($t0);
    assume {:print "$track_local(15,11,0):", $temp_0'$2_coin_Coin'#1''} $temp_0'$2_coin_Coin'#1'' == $temp_0'$2_coin_Coin'#1'';

    // destroy($t8) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:167:9+41

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:167:50+1
    $temp_0'$2_coin_Coin'#1'' := $Dereference($t0);
    assume {:print "$track_local(15,11,0):", $temp_0'$2_coin_Coin'#1''} $temp_0'$2_coin_Coin'#1'' == $temp_0'$2_coin_Coin'#1'';

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:168:5+1
    assume {:print "$at(29,5787,5788)"} true;
L1:

    // return () at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:168:5+1
    assume {:print "$at(29,5787,5788)"} true;
    $ret0 := $t0;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:168:5+1
L2:

    // abort($t6) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:168:5+1
    assume {:print "$at(29,5787,5788)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun coin::split<#0> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:180:5+161
procedure {:inline 1} $2_coin_split'#0'(_$t0: $Mutation ($2_coin_Coin'#0'), _$t1: int, _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $2_coin_Coin'#0', $ret1: $Mutation ($2_coin_Coin'#0'), $ret2: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: int;
    var $t4: $Mutation ($2_balance_Balance'#0');
    var $t5: int;
    var $t6: $2_coin_Coin'#0';
    var $t7: int;
    var $t0: $Mutation ($2_coin_Coin'#0');
    var $t1: int;
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // assume Identical($t3, select balance::Balance.value(select coin::Coin.balance($t0))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:187:9+36
    assume {:print "$at(29,6343,6379)"} true;
    assume ($t3 == $value#$2_balance_Balance'#0'($balance#$2_coin_Coin'#0'($Dereference($t0))));

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:180:5+1
    assume {:print "$at(29,6155,6156)"} true;
    $temp_0'$2_coin_Coin'#0'' := $Dereference($t0);
    assume {:print "$track_local(15,12,0):", $temp_0'$2_coin_Coin'#0''} $temp_0'$2_coin_Coin'#0'' == $temp_0'$2_coin_Coin'#0'';

    // trace_local[split_amount]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:180:5+1
    assume {:print "$track_local(15,12,1):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:180:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(15,12,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t4 := borrow_field<coin::Coin<#0>>.balance($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:14+17
    assume {:print "$at(29,6273,6290)"} true;
    $t4 := $ChildMutation($t0, 1, $balance#$2_coin_Coin'#0'($Dereference($t0)));

    // assume Identical($t5, select balance::Balance.value($t4)) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:139:9+31
    assume {:print "$at(29,4835,4866)"} true;
    assume ($t5 == $value#$2_balance_Balance'#0'($Dereference($t4)));

    // $t6 := coin::take<#0>($t4, $t1, $t2) on_abort goto L2 with $t7 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:9+42
    assume {:print "$at(29,6268,6310)"} true;
    call $t6,$t4,$t2 := $2_coin_take'#0'($t4, $t1, $t2);
    if ($abort_flag) {
        assume {:print "$at(29,6268,6310)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(15,12):", $t7} $t7 == $t7;
        goto L2;
    }

    // write_back[Reference($t0).balance (balance::Balance<#0>)]($t4) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:9+42
    $t0 := $UpdateMutation($t0, $Update'$2_coin_Coin'#0''_balance($Dereference($t0), $Dereference($t4)));

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:9+42
    $temp_0'$2_coin_Coin'#0'' := $Dereference($t0);
    assume {:print "$track_local(15,12,0):", $temp_0'$2_coin_Coin'#0''} $temp_0'$2_coin_Coin'#0'' == $temp_0'$2_coin_Coin'#0'';

    // trace_return[0]($t6) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:9+42
    assume {:print "$track_return(15,12,0):", $t6} $t6 == $t6;

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:9+42
    $temp_0'$2_coin_Coin'#0'' := $Dereference($t0);
    assume {:print "$track_local(15,12,0):", $temp_0'$2_coin_Coin'#0''} $temp_0'$2_coin_Coin'#0'' == $temp_0'$2_coin_Coin'#0'';

    // trace_local[ctx]($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:9+42
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(15,12,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:184:5+1
    assume {:print "$at(29,6315,6316)"} true;
L1:

    // return $t6 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:184:5+1
    assume {:print "$at(29,6315,6316)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    $ret2 := $t2;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:184:5+1
L2:

    // abort($t7) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:184:5+1
    assume {:print "$at(29,6315,6316)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun coin::split<#1> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:180:5+161
procedure {:inline 1} $2_coin_split'#1'(_$t0: $Mutation ($2_coin_Coin'#1'), _$t1: int, _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $2_coin_Coin'#1', $ret1: $Mutation ($2_coin_Coin'#1'), $ret2: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: int;
    var $t4: $Mutation ($2_balance_Balance'#1');
    var $t5: int;
    var $t6: $2_coin_Coin'#1';
    var $t7: int;
    var $t0: $Mutation ($2_coin_Coin'#1');
    var $t1: int;
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_coin_Coin'#1'': $2_coin_Coin'#1';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // assume Identical($t3, select balance::Balance.value(select coin::Coin.balance($t0))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:187:9+36
    assume {:print "$at(29,6343,6379)"} true;
    assume ($t3 == $value#$2_balance_Balance'#1'($balance#$2_coin_Coin'#1'($Dereference($t0))));

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:180:5+1
    assume {:print "$at(29,6155,6156)"} true;
    $temp_0'$2_coin_Coin'#1'' := $Dereference($t0);
    assume {:print "$track_local(15,12,0):", $temp_0'$2_coin_Coin'#1''} $temp_0'$2_coin_Coin'#1'' == $temp_0'$2_coin_Coin'#1'';

    // trace_local[split_amount]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:180:5+1
    assume {:print "$track_local(15,12,1):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:180:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(15,12,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t4 := borrow_field<coin::Coin<#0>>.balance($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:14+17
    assume {:print "$at(29,6273,6290)"} true;
    $t4 := $ChildMutation($t0, 1, $balance#$2_coin_Coin'#1'($Dereference($t0)));

    // assume Identical($t5, select balance::Balance.value($t4)) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:139:9+31
    assume {:print "$at(29,4835,4866)"} true;
    assume ($t5 == $value#$2_balance_Balance'#1'($Dereference($t4)));

    // $t6 := coin::take<#0>($t4, $t1, $t2) on_abort goto L2 with $t7 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:9+42
    assume {:print "$at(29,6268,6310)"} true;
    call $t6,$t4,$t2 := $2_coin_take'#1'($t4, $t1, $t2);
    if ($abort_flag) {
        assume {:print "$at(29,6268,6310)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(15,12):", $t7} $t7 == $t7;
        goto L2;
    }

    // write_back[Reference($t0).balance (balance::Balance<#0>)]($t4) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:9+42
    $t0 := $UpdateMutation($t0, $Update'$2_coin_Coin'#1''_balance($Dereference($t0), $Dereference($t4)));

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:9+42
    $temp_0'$2_coin_Coin'#1'' := $Dereference($t0);
    assume {:print "$track_local(15,12,0):", $temp_0'$2_coin_Coin'#1''} $temp_0'$2_coin_Coin'#1'' == $temp_0'$2_coin_Coin'#1'';

    // trace_return[0]($t6) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:9+42
    assume {:print "$track_return(15,12,0):", $t6} $t6 == $t6;

    // trace_local[self]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:9+42
    $temp_0'$2_coin_Coin'#1'' := $Dereference($t0);
    assume {:print "$track_local(15,12,0):", $temp_0'$2_coin_Coin'#1''} $temp_0'$2_coin_Coin'#1'' == $temp_0'$2_coin_Coin'#1'';

    // trace_local[ctx]($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:183:9+42
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(15,12,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:184:5+1
    assume {:print "$at(29,6315,6316)"} true;
L1:

    // return $t6 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:184:5+1
    assume {:print "$at(29,6315,6316)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    $ret2 := $t2;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:184:5+1
L2:

    // abort($t7) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:184:5+1
    assume {:print "$at(29,6315,6316)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun coin::zero<#0> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:233:5+120
procedure {:inline 1} $2_coin_zero'#0'(_$t0: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $2_coin_Coin'#0', $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t1: $2_object_UID;
    var $t2: int;
    var $t3: $2_balance_Balance'#0';
    var $t4: $2_coin_Coin'#0';
    var $t0: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[ctx]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:233:5+1
    assume {:print "$at(29,7930,7931)"} true;
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(15,14,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t1 := object::new($t0) on_abort goto L2 with $t2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:234:20+16
    assume {:print "$at(29,8000,8016)"} true;
    call $t1,$t0 := $2_object_new($t0);
    if ($abort_flag) {
        assume {:print "$at(29,8000,8016)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(15,14):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := balance::zero<#0>() on_abort goto L2 with $t2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:234:47+15
    call $t3 := $2_balance_zero'#0'();
    if ($abort_flag) {
        assume {:print "$at(29,8027,8042)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(15,14):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t4 := pack coin::Coin<#0>($t1, $t3) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:234:9+55
    $t4 := $2_coin_Coin'#0'($t1, $t3);

    // trace_return[0]($t4) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:234:9+55
    assume {:print "$track_return(15,14,0):", $t4} $t4 == $t4;

    // trace_local[ctx]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:234:9+55
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(15,14,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:235:5+1
    assume {:print "$at(29,8049,8050)"} true;
L1:

    // return $t4 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:235:5+1
    assume {:print "$at(29,8049,8050)"} true;
    $ret0 := $t4;
    $ret1 := $t0;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:235:5+1
L2:

    // abort($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:235:5+1
    assume {:print "$at(29,8049,8050)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun coin::take<#0> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:129:5+220
procedure {:inline 1} $2_coin_take'#0'(_$t0: $Mutation ($2_balance_Balance'#0'), _$t1: int, _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $2_coin_Coin'#0', $ret1: $Mutation ($2_balance_Balance'#0'), $ret2: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: int;
    var $t4: $2_object_UID;
    var $t5: int;
    var $t6: $2_balance_Balance'#0';
    var $t7: $2_coin_Coin'#0';
    var $t0: $Mutation ($2_balance_Balance'#0');
    var $t1: int;
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // assume Identical($t3, select balance::Balance.value($t0)) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:139:9+31
    assume {:print "$at(29,4835,4866)"} true;
    assume ($t3 == $value#$2_balance_Balance'#0'($Dereference($t0)));

    // trace_local[balance]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:129:5+1
    assume {:print "$at(29,4589,4590)"} true;
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(15,9,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // trace_local[value]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:129:5+1
    assume {:print "$track_local(15,9,1):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:129:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(15,9,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t4 := object::new($t2) on_abort goto L2 with $t5 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:133:17+16
    assume {:print "$at(29,4724,4740)"} true;
    call $t4,$t2 := $2_object_new($t2);
    if ($abort_flag) {
        assume {:print "$at(29,4724,4740)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(15,9):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t6 := balance::split<#0>($t0, $t1) on_abort goto L2 with $t5 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:134:22+30
    assume {:print "$at(29,4763,4793)"} true;
    call $t6,$t0 := $2_balance_split'#0'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(29,4763,4793)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(15,9):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t7 := pack coin::Coin<#0>($t4, $t6) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:132:9+102
    assume {:print "$at(29,4701,4803)"} true;
    $t7 := $2_coin_Coin'#0'($t4, $t6);

    // trace_return[0]($t7) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:132:9+102
    assume {:print "$track_return(15,9,0):", $t7} $t7 == $t7;

    // trace_local[balance]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:132:9+102
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(15,9,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // trace_local[ctx]($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:132:9+102
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(15,9,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:136:5+1
    assume {:print "$at(29,4808,4809)"} true;
L1:

    // return $t7 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:136:5+1
    assume {:print "$at(29,4808,4809)"} true;
    $ret0 := $t7;
    $ret1 := $t0;
    $ret2 := $t2;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:136:5+1
L2:

    // abort($t5) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:136:5+1
    assume {:print "$at(29,4808,4809)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun coin::take<#1> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:129:5+220
procedure {:inline 1} $2_coin_take'#1'(_$t0: $Mutation ($2_balance_Balance'#1'), _$t1: int, _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $2_coin_Coin'#1', $ret1: $Mutation ($2_balance_Balance'#1'), $ret2: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: int;
    var $t4: $2_object_UID;
    var $t5: int;
    var $t6: $2_balance_Balance'#1';
    var $t7: $2_coin_Coin'#1';
    var $t0: $Mutation ($2_balance_Balance'#1');
    var $t1: int;
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_balance_Balance'#1'': $2_balance_Balance'#1';
    var $temp_0'$2_coin_Coin'#1'': $2_coin_Coin'#1';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // assume Identical($t3, select balance::Balance.value($t0)) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:139:9+31
    assume {:print "$at(29,4835,4866)"} true;
    assume ($t3 == $value#$2_balance_Balance'#1'($Dereference($t0)));

    // trace_local[balance]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:129:5+1
    assume {:print "$at(29,4589,4590)"} true;
    $temp_0'$2_balance_Balance'#1'' := $Dereference($t0);
    assume {:print "$track_local(15,9,0):", $temp_0'$2_balance_Balance'#1''} $temp_0'$2_balance_Balance'#1'' == $temp_0'$2_balance_Balance'#1'';

    // trace_local[value]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:129:5+1
    assume {:print "$track_local(15,9,1):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:129:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(15,9,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t4 := object::new($t2) on_abort goto L2 with $t5 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:133:17+16
    assume {:print "$at(29,4724,4740)"} true;
    call $t4,$t2 := $2_object_new($t2);
    if ($abort_flag) {
        assume {:print "$at(29,4724,4740)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(15,9):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t6 := balance::split<#0>($t0, $t1) on_abort goto L2 with $t5 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:134:22+30
    assume {:print "$at(29,4763,4793)"} true;
    call $t6,$t0 := $2_balance_split'#1'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(29,4763,4793)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(15,9):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t7 := pack coin::Coin<#0>($t4, $t6) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:132:9+102
    assume {:print "$at(29,4701,4803)"} true;
    $t7 := $2_coin_Coin'#1'($t4, $t6);

    // trace_return[0]($t7) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:132:9+102
    assume {:print "$track_return(15,9,0):", $t7} $t7 == $t7;

    // trace_local[balance]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:132:9+102
    $temp_0'$2_balance_Balance'#1'' := $Dereference($t0);
    assume {:print "$track_local(15,9,0):", $temp_0'$2_balance_Balance'#1''} $temp_0'$2_balance_Balance'#1'' == $temp_0'$2_balance_Balance'#1'';

    // trace_local[ctx]($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:132:9+102
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(15,9,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:136:5+1
    assume {:print "$at(29,4808,4809)"} true;
L1:

    // return $t7 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:136:5+1
    assume {:print "$at(29,4808,4809)"} true;
    $ret0 := $t7;
    $ret1 := $t0;
    $ret2 := $t2;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:136:5+1
L2:

    // abort($t5) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:136:5+1
    assume {:print "$at(29,4808,4809)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// struct vec_map::Entry<address, u64> at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/vec_map.move:34:5+88
type {:datatype} $2_vec_map_Entry'address_u256';
function {:constructor} $2_vec_map_Entry'address_u256'($key: int, $value: int): $2_vec_map_Entry'address_u256';
function {:inline} $Update'$2_vec_map_Entry'address_u256''_key(s: $2_vec_map_Entry'address_u256', x: int): $2_vec_map_Entry'address_u256' {
    $2_vec_map_Entry'address_u256'(x, $value#$2_vec_map_Entry'address_u256'(s))
}
function {:inline} $Update'$2_vec_map_Entry'address_u256''_value(s: $2_vec_map_Entry'address_u256', x: int): $2_vec_map_Entry'address_u256' {
    $2_vec_map_Entry'address_u256'($key#$2_vec_map_Entry'address_u256'(s), x)
}
function $IsValid'$2_vec_map_Entry'address_u256''(s: $2_vec_map_Entry'address_u256'): bool {
    $IsValid'address'($key#$2_vec_map_Entry'address_u256'(s))
      && $IsValid'u64'($value#$2_vec_map_Entry'address_u256'(s))
}
function {:inline} $IsEqual'$2_vec_map_Entry'address_u256''(s1: $2_vec_map_Entry'address_u256', s2: $2_vec_map_Entry'address_u256'): bool {
    s1 == s2
}

// struct vec_map::VecMap<address, u64> at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/vec_map.move:29:5+94
type {:datatype} $2_vec_map_VecMap'address_u256';
function {:constructor} $2_vec_map_VecMap'address_u256'($contents: Vec ($2_vec_map_Entry'address_u256')): $2_vec_map_VecMap'address_u256';
function {:inline} $Update'$2_vec_map_VecMap'address_u256''_contents(s: $2_vec_map_VecMap'address_u256', x: Vec ($2_vec_map_Entry'address_u256')): $2_vec_map_VecMap'address_u256' {
    $2_vec_map_VecMap'address_u256'(x)
}
function $IsValid'$2_vec_map_VecMap'address_u256''(s: $2_vec_map_VecMap'address_u256'): bool {
    $IsValid'vec'$2_vec_map_Entry'address_u256'''($contents#$2_vec_map_VecMap'address_u256'(s))
}
function {:inline} $IsEqual'$2_vec_map_VecMap'address_u256''(s1: $2_vec_map_VecMap'address_u256', s2: $2_vec_map_VecMap'address_u256'): bool {
    $IsEqual'vec'$2_vec_map_Entry'address_u256'''($contents#$2_vec_map_VecMap'address_u256'(s1), $contents#$2_vec_map_VecMap'address_u256'(s2))}

// fun vec_map::empty<address, u64> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/vec_map.move:40:5+96
procedure {:inline 1} $2_vec_map_empty'address_u256'() returns ($ret0: $2_vec_map_VecMap'address_u256')
{
    // declare local variables
    var $t0: Vec ($2_vec_map_Entry'address_u256');
    var $t1: int;
    var $t2: $2_vec_map_VecMap'address_u256';
    var $temp_0'$2_vec_map_VecMap'address_u256'': $2_vec_map_VecMap'address_u256';

    // bytecode translation starts here
    // $t0 := vector::empty<vec_map::Entry<#0, #1>>() on_abort goto L2 with $t1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/vec_map.move:41:28+15
    assume {:print "$at(72,1461,1476)"} true;
    call $t0 := $1_vector_empty'$2_vec_map_Entry'address_u256''();
    if ($abort_flag) {
        assume {:print "$at(72,1461,1476)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(16,0):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := pack vec_map::VecMap<#0, #1>($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/vec_map.move:41:9+36
    $t2 := $2_vec_map_VecMap'address_u256'($t0);

    // trace_return[0]($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/vec_map.move:41:9+36
    assume {:print "$track_return(16,0,0):", $t2} $t2 == $t2;

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/vec_map.move:42:5+1
    assume {:print "$at(72,1483,1484)"} true;
L1:

    // return $t2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/vec_map.move:42:5+1
    assume {:print "$at(72,1483,1484)"} true;
    $ret0 := $t2;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/vec_map.move:42:5+1
L2:

    // abort($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/vec_map.move:42:5+1
    assume {:print "$at(72,1483,1484)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// struct vault::Vault<#0, #1> at ./sources/vault.move:21:5+213
type {:datatype} $0_vault_Vault'#0_#1';
function {:constructor} $0_vault_Vault'#0_#1'($id: $2_object_UID, $pool: $2_coin_Coin'#0', $lp_price: int, $lp_supply: int, $lp_valult: $2_coin_Coin'#1', $users: $2_vec_map_VecMap'address_u256'): $0_vault_Vault'#0_#1';
function {:inline} $Update'$0_vault_Vault'#0_#1''_id(s: $0_vault_Vault'#0_#1', x: $2_object_UID): $0_vault_Vault'#0_#1' {
    $0_vault_Vault'#0_#1'(x, $pool#$0_vault_Vault'#0_#1'(s), $lp_price#$0_vault_Vault'#0_#1'(s), $lp_supply#$0_vault_Vault'#0_#1'(s), $lp_valult#$0_vault_Vault'#0_#1'(s), $users#$0_vault_Vault'#0_#1'(s))
}
function {:inline} $Update'$0_vault_Vault'#0_#1''_pool(s: $0_vault_Vault'#0_#1', x: $2_coin_Coin'#0'): $0_vault_Vault'#0_#1' {
    $0_vault_Vault'#0_#1'($id#$0_vault_Vault'#0_#1'(s), x, $lp_price#$0_vault_Vault'#0_#1'(s), $lp_supply#$0_vault_Vault'#0_#1'(s), $lp_valult#$0_vault_Vault'#0_#1'(s), $users#$0_vault_Vault'#0_#1'(s))
}
function {:inline} $Update'$0_vault_Vault'#0_#1''_lp_price(s: $0_vault_Vault'#0_#1', x: int): $0_vault_Vault'#0_#1' {
    $0_vault_Vault'#0_#1'($id#$0_vault_Vault'#0_#1'(s), $pool#$0_vault_Vault'#0_#1'(s), x, $lp_supply#$0_vault_Vault'#0_#1'(s), $lp_valult#$0_vault_Vault'#0_#1'(s), $users#$0_vault_Vault'#0_#1'(s))
}
function {:inline} $Update'$0_vault_Vault'#0_#1''_lp_supply(s: $0_vault_Vault'#0_#1', x: int): $0_vault_Vault'#0_#1' {
    $0_vault_Vault'#0_#1'($id#$0_vault_Vault'#0_#1'(s), $pool#$0_vault_Vault'#0_#1'(s), $lp_price#$0_vault_Vault'#0_#1'(s), x, $lp_valult#$0_vault_Vault'#0_#1'(s), $users#$0_vault_Vault'#0_#1'(s))
}
function {:inline} $Update'$0_vault_Vault'#0_#1''_lp_valult(s: $0_vault_Vault'#0_#1', x: $2_coin_Coin'#1'): $0_vault_Vault'#0_#1' {
    $0_vault_Vault'#0_#1'($id#$0_vault_Vault'#0_#1'(s), $pool#$0_vault_Vault'#0_#1'(s), $lp_price#$0_vault_Vault'#0_#1'(s), $lp_supply#$0_vault_Vault'#0_#1'(s), x, $users#$0_vault_Vault'#0_#1'(s))
}
function {:inline} $Update'$0_vault_Vault'#0_#1''_users(s: $0_vault_Vault'#0_#1', x: $2_vec_map_VecMap'address_u256'): $0_vault_Vault'#0_#1' {
    $0_vault_Vault'#0_#1'($id#$0_vault_Vault'#0_#1'(s), $pool#$0_vault_Vault'#0_#1'(s), $lp_price#$0_vault_Vault'#0_#1'(s), $lp_supply#$0_vault_Vault'#0_#1'(s), $lp_valult#$0_vault_Vault'#0_#1'(s), x)
}
function $IsValid'$0_vault_Vault'#0_#1''(s: $0_vault_Vault'#0_#1'): bool {
    $IsValid'$2_object_UID'($id#$0_vault_Vault'#0_#1'(s))
      && $IsValid'$2_coin_Coin'#0''($pool#$0_vault_Vault'#0_#1'(s))
      && $IsValid'u64'($lp_price#$0_vault_Vault'#0_#1'(s))
      && $IsValid'u64'($lp_supply#$0_vault_Vault'#0_#1'(s))
      && $IsValid'$2_coin_Coin'#1''($lp_valult#$0_vault_Vault'#0_#1'(s))
      && $IsValid'$2_vec_map_VecMap'address_u256''($users#$0_vault_Vault'#0_#1'(s))
}
function {:inline} $IsEqual'$0_vault_Vault'#0_#1''(s1: $0_vault_Vault'#0_#1', s2: $0_vault_Vault'#0_#1'): bool {
    $IsEqual'$2_object_UID'($id#$0_vault_Vault'#0_#1'(s1), $id#$0_vault_Vault'#0_#1'(s2))
    && $IsEqual'$2_coin_Coin'#0''($pool#$0_vault_Vault'#0_#1'(s1), $pool#$0_vault_Vault'#0_#1'(s2))
    && $IsEqual'u64'($lp_price#$0_vault_Vault'#0_#1'(s1), $lp_price#$0_vault_Vault'#0_#1'(s2))
    && $IsEqual'u64'($lp_supply#$0_vault_Vault'#0_#1'(s1), $lp_supply#$0_vault_Vault'#0_#1'(s2))
    && $IsEqual'$2_coin_Coin'#1''($lp_valult#$0_vault_Vault'#0_#1'(s1), $lp_valult#$0_vault_Vault'#0_#1'(s2))
    && $IsEqual'$2_vec_map_VecMap'address_u256''($users#$0_vault_Vault'#0_#1'(s1), $users#$0_vault_Vault'#0_#1'(s2))}
var $0_vault_Vault'#0_#1'_$memory: $Memory $0_vault_Vault'#0_#1';

// fun vault::add_liquidity [verification] at ./sources/vault.move:42:5+741
procedure {:timeLimit 40} $0_vault_add_liquidity$verify(_$t0: $Mutation ($0_vault_Vault'#0_#1'), _$t1: $2_coin_Coin'#0', _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $Mutation ($0_vault_Vault'#0_#1'), $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: $2_coin_Coin'#0';
    var $t12: int;
    var $t13: $Mutation ($2_coin_Coin'#0');
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t20: int;
    var $t21: int;
    var $t22: int;
    var $t23: int;
    var $t24: int;
    var $t25: bool;
    var $t26: int;
    var $t27: int;
    var $t28: int;
    var $t29: int;
    var $t30: $Mutation (int);
    var $t31: $Mutation ($2_coin_Coin'#1');
    var $t32: int;
    var $t33: $2_coin_Coin'#1';
    var $t34: $2_tx_context_TxContext;
    var $t35: int;
    var $t0: $Mutation ($0_vault_Vault'#0_#1');
    var $t1: $2_coin_Coin'#0';
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$0_vault_Vault'#0_#1'': $0_vault_Vault'#0_#1';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);
    assume l#$Mutation($t2) == $Param(2);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/vault.move:42:5+1
    assume {:print "$at(4,1095,1096)"} true;
    assume $IsValid'$0_vault_Vault'#0_#1''($Dereference($t0));

    // assume WellFormed($t1) at ./sources/vault.move:42:5+1
    assume $IsValid'$2_coin_Coin'#0''($t1);

    // assume WellFormed($t2) at ./sources/vault.move:42:5+1
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t2));

    // trace_local[vau]($t0) at ./sources/vault.move:42:5+1
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,1,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[c]($t1) at ./sources/vault.move:42:5+1
    assume {:print "$track_local(18,1,1):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at ./sources/vault.move:42:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(18,1,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t9 := coin::value<#0>($t1) on_abort goto L4 with $t10 at ./sources/vault.move:43:21+15
    assume {:print "$at(4,1214,1229)"} true;
    call $t9 := $2_coin_value'#0'($t1);
    if ($abort_flag) {
        assume {:print "$at(4,1214,1229)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[value#1#0]($t9) at ./sources/vault.move:43:13+5
    assume {:print "$track_local(18,1,8):", $t9} $t9 == $t9;

    // $t11 := get_field<vault::Vault<#0, #1>>.pool($t0) at ./sources/vault.move:44:38+9
    assume {:print "$at(4,1268,1277)"} true;
    $t11 := $pool#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t12 := coin::value<#0>($t11) on_abort goto L4 with $t10 at ./sources/vault.move:44:26+22
    call $t12 := $2_coin_value'#0'($t11);
    if ($abort_flag) {
        assume {:print "$at(4,1256,1278)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[pool_value#1#0]($t12) at ./sources/vault.move:44:13+10
    assume {:print "$track_local(18,1,7):", $t12} $t12 == $t12;

    // $t13 := borrow_field<vault::Vault<#0, #1>>.pool($t0) at ./sources/vault.move:45:20+13
    assume {:print "$at(4,1299,1312)"} true;
    $t13 := $ChildMutation($t0, 1, $pool#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // assume Identical($t14, select balance::Balance.value(select coin::Coin.balance($t13))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:171:9+36
    assume {:print "$at(29,5814,5850)"} true;
    assume ($t14 == $value#$2_balance_Balance'#0'($balance#$2_coin_Coin'#0'($Dereference($t13))));

    // coin::join<#0>($t13, $t1) on_abort goto L4 with $t10 at ./sources/vault.move:45:9+28
    assume {:print "$at(4,1288,1316)"} true;
    call $t13 := $2_coin_join'#0'($t13, $t1);
    if ($abort_flag) {
        assume {:print "$at(4,1288,1316)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // write_back[Reference($t0).pool (coin::Coin<#0>)]($t13) at ./sources/vault.move:45:9+28
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_pool($Dereference($t0), $Dereference($t13)));

    // trace_local[vau]($t0) at ./sources/vault.move:45:9+28
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,1,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // $t15 := get_field<vault::Vault<#0, #1>>.lp_price($t0) at ./sources/vault.move:47:32+12
    assume {:print "$at(4,1350,1362)"} true;
    $t15 := $lp_price#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t16 := *($t12, $t15) on_abort goto L4 with $t10 at ./sources/vault.move:47:30+1
    call $t16 := $Mulu256($t12, $t15);
    if ($abort_flag) {
        assume {:print "$at(4,1348,1349)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // $t17 := 100000000 at ./sources/vault.move:47:47+11
    $t17 := 100000000;
    assume $IsValid'u64'($t17);

    // $t18 := /($t16, $t17) on_abort goto L4 with $t10 at ./sources/vault.move:47:45+1
    call $t18 := $Div($t16, $t17);
    if ($abort_flag) {
        assume {:print "$at(4,1363,1364)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[amt#1#0]($t18) at ./sources/vault.move:47:13+3
    assume {:print "$track_local(18,1,3):", $t18} $t18 == $t18;

    // $t19 := get_field<vault::Vault<#0, #1>>.lp_supply($t0) at ./sources/vault.move:48:26+13
    assume {:print "$at(4,1403,1416)"} true;
    $t19 := $lp_supply#$0_vault_Vault'#0_#1'($Dereference($t0));

    // trace_local[llp_supply#1#0]($t19) at ./sources/vault.move:48:13+10
    assume {:print "$track_local(18,1,4):", $t19} $t19 == $t19;

    // $t20 := get_field<vault::Vault<#0, #1>>.lp_price($t0) at ./sources/vault.move:50:26+12
    assume {:print "$at(4,1444,1456)"} true;
    $t20 := $lp_price#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t21 := *($t9, $t20) on_abort goto L4 with $t10 at ./sources/vault.move:50:24+1
    call $t21 := $Mulu256($t9, $t20);
    if ($abort_flag) {
        assume {:print "$at(4,1442,1443)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // $t22 := 100000000 at ./sources/vault.move:50:41+11
    $t22 := 100000000;
    assume $IsValid'u64'($t22);

    // $t23 := /($t21, $t22) on_abort goto L4 with $t10 at ./sources/vault.move:50:39+1
    call $t23 := $Div($t21, $t22);
    if ($abort_flag) {
        assume {:print "$at(4,1457,1458)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[lp#1#0]($t23) at ./sources/vault.move:50:13+2
    assume {:print "$track_local(18,1,5):", $t23} $t23 == $t23;

    // $t24 := 0 at ./sources/vault.move:54:20+1
    assume {:print "$at(4,1512,1513)"} true;
    $t24 := 0;
    assume $IsValid'u64'($t24);

    // $t25 := ==($t18, $t24) at ./sources/vault.move:54:17+2
    $t25 := $IsEqual'u64'($t18, $t24);

    // if ($t25) goto L1 else goto L0 at ./sources/vault.move:54:9+162
    if ($t25) { goto L1; } else { goto L0; }

    // label L1 at ./sources/vault.move:55:20+2
    assume {:print "$at(4,1536,1538)"} true;
L1:

    // $t6 := $t23 at ./sources/vault.move:55:13+4
    assume {:print "$at(4,1529,1533)"} true;
    $t6 := $t23;

    // trace_local[mint#1#0]($t23) at ./sources/vault.move:55:13+4
    assume {:print "$track_local(18,1,6):", $t23} $t23 == $t23;

    // goto L2 at ./sources/vault.move:55:22+1
    goto L2;

    // label L0 at ./sources/vault.move:58:20+2
    assume {:print "$at(4,1631,1633)"} true;
L0:

    // $t26 := *($t23, $t19) on_abort goto L4 with $t10 at ./sources/vault.move:58:23+1
    assume {:print "$at(4,1634,1635)"} true;
    call $t26 := $Mulu256($t23, $t19);
    if ($abort_flag) {
        assume {:print "$at(4,1634,1635)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // $t27 := /($t26, $t18) on_abort goto L4 with $t10 at ./sources/vault.move:58:36+1
    call $t27 := $Div($t26, $t18);
    if ($abort_flag) {
        assume {:print "$at(4,1647,1648)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // $t6 := $t27 at ./sources/vault.move:58:13+4
    $t6 := $t27;

    // trace_local[mint#1#0]($t27) at ./sources/vault.move:58:13+4
    assume {:print "$track_local(18,1,6):", $t27} $t27 == $t27;

    // label L2 at ./sources/vault.move:61:25+3
    assume {:print "$at(4,1690,1693)"} true;
L2:

    // $t28 := get_field<vault::Vault<#0, #1>>.lp_supply($t0) at ./sources/vault.move:61:25+13
    assume {:print "$at(4,1690,1703)"} true;
    $t28 := $lp_supply#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t29 := +($t28, $t6) on_abort goto L4 with $t10 at ./sources/vault.move:61:39+1
    call $t29 := $Addu256($t28, $t6);
    if ($abort_flag) {
        assume {:print "$at(4,1704,1705)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // $t30 := borrow_field<vault::Vault<#0, #1>>.lp_supply($t0) at ./sources/vault.move:61:9+13
    $t30 := $ChildMutation($t0, 3, $lp_supply#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // write_ref($t30, $t29) at ./sources/vault.move:61:9+36
    $t30 := $UpdateMutation($t30, $t29);

    // write_back[Reference($t0).lp_supply (u64)]($t30) at ./sources/vault.move:61:9+36
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_lp_supply($Dereference($t0), $Dereference($t30)));

    // trace_local[vau]($t0) at ./sources/vault.move:61:9+36
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,1,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // $t31 := borrow_field<vault::Vault<#0, #1>>.lp_valult($t0) at ./sources/vault.move:62:32+18
    assume {:print "$at(4,1743,1761)"} true;
    $t31 := $ChildMutation($t0, 4, $lp_valult#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // assume Identical($t32, select balance::Balance.value(select coin::Coin.balance($t31))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:187:9+36
    assume {:print "$at(29,6343,6379)"} true;
    assume ($t32 == $value#$2_balance_Balance'#1'($balance#$2_coin_Coin'#1'($Dereference($t31))));

    // $t33 := coin::split<#1>($t31, $t6, $t2) on_abort goto L4 with $t10 at ./sources/vault.move:62:20+42
    assume {:print "$at(4,1731,1773)"} true;
    call $t33,$t31,$t2 := $2_coin_split'#1'($t31, $t6, $t2);
    if ($abort_flag) {
        assume {:print "$at(4,1731,1773)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // write_back[Reference($t0).lp_valult (coin::Coin<#1>)]($t31) at ./sources/vault.move:62:20+42
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_lp_valult($Dereference($t0), $Dereference($t31)));

    // trace_local[vau]($t0) at ./sources/vault.move:62:20+42
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,1,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // $t34 := read_ref($t2) at ./sources/vault.move:63:50+3
    assume {:print "$at(4,1824,1827)"} true;
    $t34 := $Dereference($t2);

    // $t35 := tx_context::sender($t34) on_abort goto L4 with $t10 at ./sources/vault.move:63:31+23
    call $t35 := $2_tx_context_sender($t34);
    if ($abort_flag) {
        assume {:print "$at(4,1805,1828)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // transfer::public_transfer<coin::Coin<#1>>($t33, $t35) on_abort goto L4 with $t10 at ./sources/vault.move:63:9+46
    call $2_transfer_public_transfer'$2_coin_Coin'#1''($t33, $t35);
    if ($abort_flag) {
        assume {:print "$at(4,1783,1829)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(18,1):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[vau]($t0) at ./sources/vault.move:63:55+1
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,1,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[ctx]($t2) at ./sources/vault.move:63:55+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(18,1,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L3 at ./sources/vault.move:64:5+1
    assume {:print "$at(4,1835,1836)"} true;
L3:

    // return () at ./sources/vault.move:64:5+1
    assume {:print "$at(4,1835,1836)"} true;
    $ret0 := $t0;
    $ret1 := $t2;
    return;

    // label L4 at ./sources/vault.move:64:5+1
L4:

    // abort($t10) at ./sources/vault.move:64:5+1
    assume {:print "$at(4,1835,1836)"} true;
    $abort_code := $t10;
    $abort_flag := true;
    return;

}

// fun vault::init_value [verification] at ./sources/vault.move:31:5+328
procedure {:timeLimit 40} $0_vault_init_value$verify(_$t0: $2_coin_Coin'#1', _$t1: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t2: $2_object_UID;
    var $t3: int;
    var $t4: $2_coin_Coin'#0';
    var $t5: int;
    var $t6: int;
    var $t7: $2_vec_map_VecMap'address_u256';
    var $t8: $0_vault_Vault'#0_#1';
    var $t0: $2_coin_Coin'#1';
    var $t1: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_coin_Coin'#1'': $2_coin_Coin'#1';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t1) == $Param(1);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/vault.move:31:5+1
    assume {:print "$at(4,761,762)"} true;
    assume $IsValid'$2_coin_Coin'#1''($t0);

    // assume WellFormed($t1) at ./sources/vault.move:31:5+1
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t1));

    // trace_local[lp]($t0) at ./sources/vault.move:31:5+1
    assume {:print "$track_local(18,0,0):", $t0} $t0 == $t0;

    // trace_local[ctx]($t1) at ./sources/vault.move:31:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t1);
    assume {:print "$track_local(18,0,1):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t2 := object::new($t1) on_abort goto L2 with $t3 at ./sources/vault.move:33:17+16
    assume {:print "$at(4,895,911)"} true;
    call $t2,$t1 := $2_object_new($t1);
    if ($abort_flag) {
        assume {:print "$at(4,895,911)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(18,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := coin::zero<#0>($t1) on_abort goto L2 with $t3 at ./sources/vault.move:34:19+18
    assume {:print "$at(4,931,949)"} true;
    call $t4,$t1 := $2_coin_zero'#0'($t1);
    if ($abort_flag) {
        assume {:print "$at(4,931,949)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(18,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t5 := 100000000 at ./sources/vault.move:35:23+8
    assume {:print "$at(4,973,981)"} true;
    $t5 := 100000000;
    assume $IsValid'u64'($t5);

    // $t6 := 0 at ./sources/vault.move:36:24+1
    assume {:print "$at(4,1006,1007)"} true;
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // $t7 := vec_map::empty<address, u64>() on_abort goto L2 with $t3 at ./sources/vault.move:38:20+16
    assume {:print "$at(4,1055,1071)"} true;
    call $t7 := $2_vec_map_empty'address_u256'();
    if ($abort_flag) {
        assume {:print "$at(4,1055,1071)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(18,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t8 := pack vault::Vault<#0, #1>($t2, $t4, $t5, $t6, $t0, $t7) at ./sources/vault.move:32:29+219
    assume {:print "$at(4,863,1082)"} true;
    $t8 := $0_vault_Vault'#0_#1'($t2, $t4, $t5, $t6, $t0, $t7);

    // transfer::public_share_object<vault::Vault<#0, #1>>($t8) on_abort goto L2 with $t3 at ./sources/vault.move:32:9+240
    call $2_transfer_public_share_object'$0_vault_Vault'#0_#1''($t8);
    if ($abort_flag) {
        assume {:print "$at(4,843,1083)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(18,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_local[ctx]($t1) at ./sources/vault.move:32:9+240
    $temp_0'$2_tx_context_TxContext' := $Dereference($t1);
    assume {:print "$track_local(18,0,1):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./sources/vault.move:40:5+1
    assume {:print "$at(4,1088,1089)"} true;
L1:

    // return () at ./sources/vault.move:40:5+1
    assume {:print "$at(4,1088,1089)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/vault.move:40:5+1
L2:

    // abort($t3) at ./sources/vault.move:40:5+1
    assume {:print "$at(4,1088,1089)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun vault::lose<#0, #1> [baseline] at ./sources/vault.move:101:5+597
procedure {:inline 1} $0_vault_lose'#0_#1'(_$t0: $Mutation ($0_vault_Vault'#0_#1'), _$t1: $2_coin_Coin'#0', _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $2_coin_Coin'#0', $ret1: $Mutation ($0_vault_Vault'#0_#1'), $ret2: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $2_coin_Coin'#0';
    var $t8: int;
    var $t9: $2_coin_Coin'#0';
    var $t10: int;
    var $t11: int;
    var $t12: $2_coin_Coin'#0';
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t20: int;
    var $t21: int;
    var $t22: $0_vault_Vault'#0_#1';
    var $t23: $Mutation (int);
    var $t24: int;
    var $t25: int;
    var $t26: int;
    var $t27: int;
    var $t28: $Mutation ($2_coin_Coin'#0');
    var $t29: int;
    var $t30: int;
    var $t31: $2_coin_Coin'#0';
    var $t32: $Mutation ($2_coin_Coin'#0');
    var $t33: int;
    var $t34: $2_coin_Coin'#0';
    var $t0: $Mutation ($0_vault_Vault'#0_#1');
    var $t1: $2_coin_Coin'#0';
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$0_vault_Vault'#0_#1'': $0_vault_Vault'#0_#1';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[vau]($t0) at ./sources/vault.move:101:5+1
    assume {:print "$at(4,2889,2890)"} true;
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,4,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[c]($t1) at ./sources/vault.move:101:5+1
    assume {:print "$track_local(18,4,1):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at ./sources/vault.move:101:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(18,4,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t9 := copy($t1) at ./sources/vault.move:102:33+2
    assume {:print "$at(4,3014,3016)"} true;
    $t9 := $t1;

    // $t10 := coin::value<#0>($t9) on_abort goto L2 with $t11 at ./sources/vault.move:102:21+15
    call $t10 := $2_coin_value'#0'($t9);
    if ($abort_flag) {
        assume {:print "$at(4,3002,3017)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // trace_local[value#1#0]($t10) at ./sources/vault.move:102:13+5
    assume {:print "$track_local(18,4,8):", $t10} $t10 == $t10;

    // $t12 := get_field<vault::Vault<#0, #1>>.pool($t0) at ./sources/vault.move:103:38+9
    assume {:print "$at(4,3056,3065)"} true;
    $t12 := $pool#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t13 := coin::value<#0>($t12) on_abort goto L2 with $t11 at ./sources/vault.move:103:26+22
    call $t13 := $2_coin_value'#0'($t12);
    if ($abort_flag) {
        assume {:print "$at(4,3044,3066)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // trace_local[pool_value#1#0]($t13) at ./sources/vault.move:103:13+10
    assume {:print "$track_local(18,4,6):", $t13} $t13 == $t13;

    // $t14 := get_field<vault::Vault<#0, #1>>.lp_price($t0) at ./sources/vault.move:105:30+12
    assume {:print "$at(4,3098,3110)"} true;
    $t14 := $lp_price#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t15 := *($t10, $t14) on_abort goto L2 with $t11 at ./sources/vault.move:105:28+1
    call $t15 := $Mulu256($t10, $t14);
    if ($abort_flag) {
        assume {:print "$at(4,3096,3097)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // $t16 := 100000000 at ./sources/vault.move:105:45+11
    $t16 := 100000000;
    assume $IsValid'u64'($t16);

    // $t17 := /($t15, $t16) on_abort goto L2 with $t11 at ./sources/vault.move:105:43+1
    call $t17 := $Div($t15, $t16);
    if ($abort_flag) {
        assume {:print "$at(4,3111,3112)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // trace_local[amount#1#0]($t17) at ./sources/vault.move:105:13+6
    assume {:print "$track_local(18,4,3):", $t17} $t17 == $t17;

    // $t18 := -($t13, $t17) on_abort goto L2 with $t11 at ./sources/vault.move:107:37+1
    assume {:print "$at(4,3163,3164)"} true;
    call $t18 := $Sub($t13, $t17);
    if ($abort_flag) {
        assume {:print "$at(4,3163,3164)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // $t19 := 100000000 at ./sources/vault.move:108:37+11
    assume {:print "$at(4,3209,3220)"} true;
    $t19 := 100000000;
    assume $IsValid'u64'($t19);

    // $t20 := *($t18, $t19) on_abort goto L2 with $t11 at ./sources/vault.move:108:35+1
    call $t20 := $Mulu256($t18, $t19);
    if ($abort_flag) {
        assume {:print "$at(4,3207,3208)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // $t21 := /($t20, $t13) on_abort goto L2 with $t11 at ./sources/vault.move:108:49+1
    call $t21 := $Div($t20, $t13);
    if ($abort_flag) {
        assume {:print "$at(4,3221,3222)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // trace_local[lp_price#1#0]($t21) at ./sources/vault.move:108:13+8
    assume {:print "$track_local(18,4,5):", $t21} $t21 == $t21;

    // debug::print<u64>($t21) on_abort goto L2 with $t11 at ./sources/vault.move:110:9+16
    assume {:print "$at(4,3244,3260)"} true;
    call $1_debug_print'u64'($t21);
    if ($abort_flag) {
        assume {:print "$at(4,3244,3260)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // $t22 := read_ref($t0) at ./sources/vault.move:111:15+3
    assume {:print "$at(4,3276,3279)"} true;
    $t22 := $Dereference($t0);

    // debug::print<vault::Vault<#0, #1>>($t22) on_abort goto L2 with $t11 at ./sources/vault.move:111:9+10
    call $1_debug_print'$0_vault_Vault'#0_#1''($t22);
    if ($abort_flag) {
        assume {:print "$at(4,3270,3280)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // $t23 := borrow_field<vault::Vault<#0, #1>>.lp_price($t0) at ./sources/vault.move:112:9+12
    assume {:print "$at(4,3290,3302)"} true;
    $t23 := $ChildMutation($t0, 2, $lp_price#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // write_ref($t23, $t21) at ./sources/vault.move:112:9+23
    $t23 := $UpdateMutation($t23, $t21);

    // write_back[Reference($t0).lp_price (u64)]($t23) at ./sources/vault.move:112:9+23
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_lp_price($Dereference($t0), $Dereference($t23)));

    // trace_local[vau]($t0) at ./sources/vault.move:112:9+23
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,4,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // $t24 := 500 at ./sources/vault.move:114:27+3
    assume {:print "$at(4,3342,3345)"} true;
    $t24 := 500;
    assume $IsValid'u64'($t24);

    // $t25 := *($t10, $t24) on_abort goto L2 with $t11 at ./sources/vault.move:114:25+1
    call $t25 := $Mulu256($t10, $t24);
    if ($abort_flag) {
        assume {:print "$at(4,3340,3341)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // $t26 := 10000 at ./sources/vault.move:114:33+20
    $t26 := 10000;
    assume $IsValid'u64'($t26);

    // $t27 := /($t25, $t26) on_abort goto L2 with $t11 at ./sources/vault.move:114:31+1
    call $t27 := $Div($t25, $t26);
    if ($abort_flag) {
        assume {:print "$at(4,3346,3347)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // trace_local[fee#1#0]($t27) at ./sources/vault.move:114:13+3
    assume {:print "$track_local(18,4,4):", $t27} $t27 == $t27;

    // $t28 := borrow_field<vault::Vault<#0, #1>>.pool($t0) at ./sources/vault.move:115:33+13
    assume {:print "$at(4,3402,3415)"} true;
    $t28 := $ChildMutation($t0, 1, $pool#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // $t29 := -($t10, $t27) on_abort goto L2 with $t11 at ./sources/vault.move:115:54+1
    call $t29 := $Sub($t10, $t27);
    if ($abort_flag) {
        assume {:print "$at(4,3423,3424)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // assume Identical($t30, select balance::Balance.value(select coin::Coin.balance($t28))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:187:9+36
    assume {:print "$at(29,6343,6379)"} true;
    assume ($t30 == $value#$2_balance_Balance'#0'($balance#$2_coin_Coin'#0'($Dereference($t28))));

    // $t31 := coin::split<#0>($t28, $t29, $t2) on_abort goto L2 with $t11 at ./sources/vault.move:115:21+44
    assume {:print "$at(4,3390,3434)"} true;
    call $t31,$t28,$t2 := $2_coin_split'#0'($t28, $t29, $t2);
    if ($abort_flag) {
        assume {:print "$at(4,3390,3434)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // write_back[Reference($t0).pool (coin::Coin<#0>)]($t28) at ./sources/vault.move:115:21+44
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_pool($Dereference($t0), $Dereference($t28)));

    // trace_local[vau]($t0) at ./sources/vault.move:115:21+44
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,4,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[split#1#0]($t31) at ./sources/vault.move:115:13+5
    assume {:print "$track_local(18,4,7):", $t31} $t31 == $t31;

    // $t32 := borrow_local($t1) at ./sources/vault.move:116:20+6
    assume {:print "$at(4,3455,3461)"} true;
    $t32 := $Mutation($Local(1), EmptyVec(), $t1);

    // assume Identical($t33, select balance::Balance.value(select coin::Coin.balance($t32))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:171:9+36
    assume {:print "$at(29,5814,5850)"} true;
    assume ($t33 == $value#$2_balance_Balance'#0'($balance#$2_coin_Coin'#0'($Dereference($t32))));

    // coin::join<#0>($t32, $t31) on_abort goto L2 with $t11 at ./sources/vault.move:116:9+25
    assume {:print "$at(4,3444,3469)"} true;
    call $t32 := $2_coin_join'#0'($t32, $t31);
    if ($abort_flag) {
        assume {:print "$at(4,3444,3469)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // write_back[LocalRoot($t1)@]($t32) at ./sources/vault.move:116:9+25
    $t1 := $Dereference($t32);

    // trace_local[c]($t1) at ./sources/vault.move:116:9+25
    assume {:print "$track_local(18,4,1):", $t1} $t1 == $t1;

    // $t34 := move($t1) at ./sources/vault.move:117:9+1
    assume {:print "$at(4,3479,3480)"} true;
    $t34 := $t1;

    // trace_return[0]($t34) at ./sources/vault.move:117:9+1
    assume {:print "$track_return(18,4,0):", $t34} $t34 == $t34;

    // trace_local[vau]($t0) at ./sources/vault.move:117:9+1
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,4,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[ctx]($t2) at ./sources/vault.move:117:9+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(18,4,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./sources/vault.move:118:5+1
    assume {:print "$at(4,3485,3486)"} true;
L1:

    // return $t34 at ./sources/vault.move:118:5+1
    assume {:print "$at(4,3485,3486)"} true;
    $ret0 := $t34;
    $ret1 := $t0;
    $ret2 := $t2;
    return;

    // label L2 at ./sources/vault.move:118:5+1
L2:

    // abort($t11) at ./sources/vault.move:118:5+1
    assume {:print "$at(4,3485,3486)"} true;
    $abort_code := $t11;
    $abort_flag := true;
    return;

}

// fun vault::lose [verification] at ./sources/vault.move:101:5+597
procedure {:timeLimit 40} $0_vault_lose$verify(_$t0: $Mutation ($0_vault_Vault'#0_#1'), _$t1: $2_coin_Coin'#0', _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $2_coin_Coin'#0', $ret1: $Mutation ($0_vault_Vault'#0_#1'), $ret2: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $2_coin_Coin'#0';
    var $t8: int;
    var $t9: $2_coin_Coin'#0';
    var $t10: int;
    var $t11: int;
    var $t12: $2_coin_Coin'#0';
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t20: int;
    var $t21: int;
    var $t22: $0_vault_Vault'#0_#1';
    var $t23: $Mutation (int);
    var $t24: int;
    var $t25: int;
    var $t26: int;
    var $t27: int;
    var $t28: $Mutation ($2_coin_Coin'#0');
    var $t29: int;
    var $t30: int;
    var $t31: $2_coin_Coin'#0';
    var $t32: $Mutation ($2_coin_Coin'#0');
    var $t33: int;
    var $t34: $2_coin_Coin'#0';
    var $t0: $Mutation ($0_vault_Vault'#0_#1');
    var $t1: $2_coin_Coin'#0';
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$0_vault_Vault'#0_#1'': $0_vault_Vault'#0_#1';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);
    assume l#$Mutation($t2) == $Param(2);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/vault.move:101:5+1
    assume {:print "$at(4,2889,2890)"} true;
    assume $IsValid'$0_vault_Vault'#0_#1''($Dereference($t0));

    // assume WellFormed($t1) at ./sources/vault.move:101:5+1
    assume $IsValid'$2_coin_Coin'#0''($t1);

    // assume WellFormed($t2) at ./sources/vault.move:101:5+1
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t2));

    // trace_local[vau]($t0) at ./sources/vault.move:101:5+1
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,4,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[c]($t1) at ./sources/vault.move:101:5+1
    assume {:print "$track_local(18,4,1):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at ./sources/vault.move:101:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(18,4,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t9 := copy($t1) at ./sources/vault.move:102:33+2
    assume {:print "$at(4,3014,3016)"} true;
    $t9 := $t1;

    // $t10 := coin::value<#0>($t9) on_abort goto L2 with $t11 at ./sources/vault.move:102:21+15
    call $t10 := $2_coin_value'#0'($t9);
    if ($abort_flag) {
        assume {:print "$at(4,3002,3017)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // trace_local[value#1#0]($t10) at ./sources/vault.move:102:13+5
    assume {:print "$track_local(18,4,8):", $t10} $t10 == $t10;

    // $t12 := get_field<vault::Vault<#0, #1>>.pool($t0) at ./sources/vault.move:103:38+9
    assume {:print "$at(4,3056,3065)"} true;
    $t12 := $pool#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t13 := coin::value<#0>($t12) on_abort goto L2 with $t11 at ./sources/vault.move:103:26+22
    call $t13 := $2_coin_value'#0'($t12);
    if ($abort_flag) {
        assume {:print "$at(4,3044,3066)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // trace_local[pool_value#1#0]($t13) at ./sources/vault.move:103:13+10
    assume {:print "$track_local(18,4,6):", $t13} $t13 == $t13;

    // $t14 := get_field<vault::Vault<#0, #1>>.lp_price($t0) at ./sources/vault.move:105:30+12
    assume {:print "$at(4,3098,3110)"} true;
    $t14 := $lp_price#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t15 := *($t10, $t14) on_abort goto L2 with $t11 at ./sources/vault.move:105:28+1
    call $t15 := $Mulu256($t10, $t14);
    if ($abort_flag) {
        assume {:print "$at(4,3096,3097)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // $t16 := 100000000 at ./sources/vault.move:105:45+11
    $t16 := 100000000;
    assume $IsValid'u64'($t16);

    // $t17 := /($t15, $t16) on_abort goto L2 with $t11 at ./sources/vault.move:105:43+1
    call $t17 := $Div($t15, $t16);
    if ($abort_flag) {
        assume {:print "$at(4,3111,3112)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // trace_local[amount#1#0]($t17) at ./sources/vault.move:105:13+6
    assume {:print "$track_local(18,4,3):", $t17} $t17 == $t17;

    // $t18 := -($t13, $t17) on_abort goto L2 with $t11 at ./sources/vault.move:107:37+1
    assume {:print "$at(4,3163,3164)"} true;
    call $t18 := $Sub($t13, $t17);
    if ($abort_flag) {
        assume {:print "$at(4,3163,3164)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // $t19 := 100000000 at ./sources/vault.move:108:37+11
    assume {:print "$at(4,3209,3220)"} true;
    $t19 := 100000000;
    assume $IsValid'u64'($t19);

    // $t20 := *($t18, $t19) on_abort goto L2 with $t11 at ./sources/vault.move:108:35+1
    call $t20 := $Mulu256($t18, $t19);
    if ($abort_flag) {
        assume {:print "$at(4,3207,3208)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // $t21 := /($t20, $t13) on_abort goto L2 with $t11 at ./sources/vault.move:108:49+1
    call $t21 := $Div($t20, $t13);
    if ($abort_flag) {
        assume {:print "$at(4,3221,3222)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // trace_local[lp_price#1#0]($t21) at ./sources/vault.move:108:13+8
    assume {:print "$track_local(18,4,5):", $t21} $t21 == $t21;

    // debug::print<u64>($t21) on_abort goto L2 with $t11 at ./sources/vault.move:110:9+16
    assume {:print "$at(4,3244,3260)"} true;
    call $1_debug_print'u64'($t21);
    if ($abort_flag) {
        assume {:print "$at(4,3244,3260)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // $t22 := read_ref($t0) at ./sources/vault.move:111:15+3
    assume {:print "$at(4,3276,3279)"} true;
    $t22 := $Dereference($t0);

    // debug::print<vault::Vault<#0, #1>>($t22) on_abort goto L2 with $t11 at ./sources/vault.move:111:9+10
    call $1_debug_print'$0_vault_Vault'#0_#1''($t22);
    if ($abort_flag) {
        assume {:print "$at(4,3270,3280)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // $t23 := borrow_field<vault::Vault<#0, #1>>.lp_price($t0) at ./sources/vault.move:112:9+12
    assume {:print "$at(4,3290,3302)"} true;
    $t23 := $ChildMutation($t0, 2, $lp_price#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // write_ref($t23, $t21) at ./sources/vault.move:112:9+23
    $t23 := $UpdateMutation($t23, $t21);

    // write_back[Reference($t0).lp_price (u64)]($t23) at ./sources/vault.move:112:9+23
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_lp_price($Dereference($t0), $Dereference($t23)));

    // trace_local[vau]($t0) at ./sources/vault.move:112:9+23
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,4,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // $t24 := 500 at ./sources/vault.move:114:27+3
    assume {:print "$at(4,3342,3345)"} true;
    $t24 := 500;
    assume $IsValid'u64'($t24);

    // $t25 := *($t10, $t24) on_abort goto L2 with $t11 at ./sources/vault.move:114:25+1
    call $t25 := $Mulu256($t10, $t24);
    if ($abort_flag) {
        assume {:print "$at(4,3340,3341)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // $t26 := 10000 at ./sources/vault.move:114:33+20
    $t26 := 10000;
    assume $IsValid'u64'($t26);

    // $t27 := /($t25, $t26) on_abort goto L2 with $t11 at ./sources/vault.move:114:31+1
    call $t27 := $Div($t25, $t26);
    if ($abort_flag) {
        assume {:print "$at(4,3346,3347)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // trace_local[fee#1#0]($t27) at ./sources/vault.move:114:13+3
    assume {:print "$track_local(18,4,4):", $t27} $t27 == $t27;

    // $t28 := borrow_field<vault::Vault<#0, #1>>.pool($t0) at ./sources/vault.move:115:33+13
    assume {:print "$at(4,3402,3415)"} true;
    $t28 := $ChildMutation($t0, 1, $pool#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // $t29 := -($t10, $t27) on_abort goto L2 with $t11 at ./sources/vault.move:115:54+1
    call $t29 := $Sub($t10, $t27);
    if ($abort_flag) {
        assume {:print "$at(4,3423,3424)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // assume Identical($t30, select balance::Balance.value(select coin::Coin.balance($t28))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:187:9+36
    assume {:print "$at(29,6343,6379)"} true;
    assume ($t30 == $value#$2_balance_Balance'#0'($balance#$2_coin_Coin'#0'($Dereference($t28))));

    // $t31 := coin::split<#0>($t28, $t29, $t2) on_abort goto L2 with $t11 at ./sources/vault.move:115:21+44
    assume {:print "$at(4,3390,3434)"} true;
    call $t31,$t28,$t2 := $2_coin_split'#0'($t28, $t29, $t2);
    if ($abort_flag) {
        assume {:print "$at(4,3390,3434)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // write_back[Reference($t0).pool (coin::Coin<#0>)]($t28) at ./sources/vault.move:115:21+44
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_pool($Dereference($t0), $Dereference($t28)));

    // trace_local[vau]($t0) at ./sources/vault.move:115:21+44
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,4,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[split#1#0]($t31) at ./sources/vault.move:115:13+5
    assume {:print "$track_local(18,4,7):", $t31} $t31 == $t31;

    // $t32 := borrow_local($t1) at ./sources/vault.move:116:20+6
    assume {:print "$at(4,3455,3461)"} true;
    $t32 := $Mutation($Local(1), EmptyVec(), $t1);

    // assume Identical($t33, select balance::Balance.value(select coin::Coin.balance($t32))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:171:9+36
    assume {:print "$at(29,5814,5850)"} true;
    assume ($t33 == $value#$2_balance_Balance'#0'($balance#$2_coin_Coin'#0'($Dereference($t32))));

    // coin::join<#0>($t32, $t31) on_abort goto L2 with $t11 at ./sources/vault.move:116:9+25
    assume {:print "$at(4,3444,3469)"} true;
    call $t32 := $2_coin_join'#0'($t32, $t31);
    if ($abort_flag) {
        assume {:print "$at(4,3444,3469)"} true;
        $t11 := $abort_code;
        assume {:print "$track_abort(18,4):", $t11} $t11 == $t11;
        goto L2;
    }

    // write_back[LocalRoot($t1)@]($t32) at ./sources/vault.move:116:9+25
    $t1 := $Dereference($t32);

    // trace_local[c]($t1) at ./sources/vault.move:116:9+25
    assume {:print "$track_local(18,4,1):", $t1} $t1 == $t1;

    // $t34 := move($t1) at ./sources/vault.move:117:9+1
    assume {:print "$at(4,3479,3480)"} true;
    $t34 := $t1;

    // trace_return[0]($t34) at ./sources/vault.move:117:9+1
    assume {:print "$track_return(18,4,0):", $t34} $t34 == $t34;

    // trace_local[vau]($t0) at ./sources/vault.move:117:9+1
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,4,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[ctx]($t2) at ./sources/vault.move:117:9+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(18,4,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./sources/vault.move:118:5+1
    assume {:print "$at(4,3485,3486)"} true;
L1:

    // return $t34 at ./sources/vault.move:118:5+1
    assume {:print "$at(4,3485,3486)"} true;
    $ret0 := $t34;
    $ret1 := $t0;
    $ret2 := $t2;
    return;

    // label L2 at ./sources/vault.move:118:5+1
L2:

    // abort($t11) at ./sources/vault.move:118:5+1
    assume {:print "$at(4,3485,3486)"} true;
    $abort_code := $t11;
    $abort_flag := true;
    return;

}

// fun vault::remove_liquidity [verification] at ./sources/vault.move:66:5+597
procedure {:timeLimit 40} $0_vault_remove_liquidity$verify(_$t0: $Mutation ($0_vault_Vault'#0_#1'), _$t1: $2_coin_Coin'#1', _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $Mutation ($0_vault_Vault'#0_#1'), $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: $2_coin_Coin'#0';
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t20: $Mutation (int);
    var $t21: $Mutation ($2_coin_Coin'#1');
    var $t22: int;
    var $t23: $Mutation ($2_coin_Coin'#0');
    var $t24: int;
    var $t25: $2_coin_Coin'#0';
    var $t26: $2_tx_context_TxContext;
    var $t27: int;
    var $t0: $Mutation ($0_vault_Vault'#0_#1');
    var $t1: $2_coin_Coin'#1';
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$0_vault_Vault'#0_#1'': $0_vault_Vault'#0_#1';
    var $temp_0'$2_coin_Coin'#1'': $2_coin_Coin'#1';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);
    assume l#$Mutation($t2) == $Param(2);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/vault.move:66:5+1
    assume {:print "$at(4,1842,1843)"} true;
    assume $IsValid'$0_vault_Vault'#0_#1''($Dereference($t0));

    // assume WellFormed($t1) at ./sources/vault.move:66:5+1
    assume $IsValid'$2_coin_Coin'#1''($t1);

    // assume WellFormed($t2) at ./sources/vault.move:66:5+1
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t2));

    // trace_local[vau]($t0) at ./sources/vault.move:66:5+1
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,2,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[c]($t1) at ./sources/vault.move:66:5+1
    assume {:print "$track_local(18,2,1):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at ./sources/vault.move:66:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(18,2,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t7 := coin::value<#1>($t1) on_abort goto L2 with $t8 at ./sources/vault.move:67:21+15
    assume {:print "$at(4,1966,1981)"} true;
    call $t7 := $2_coin_value'#1'($t1);
    if ($abort_flag) {
        assume {:print "$at(4,1966,1981)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[value#1#0]($t7) at ./sources/vault.move:67:13+5
    assume {:print "$track_local(18,2,6):", $t7} $t7 == $t7;

    // debug::print<u64>($t7) on_abort goto L2 with $t8 at ./sources/vault.move:68:9+13
    assume {:print "$at(4,1991,2004)"} true;
    call $1_debug_print'u64'($t7);
    if ($abort_flag) {
        assume {:print "$at(4,1991,2004)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t9 := get_field<vault::Vault<#0, #1>>.pool($t0) at ./sources/vault.move:70:38+9
    assume {:print "$at(4,2044,2053)"} true;
    $t9 := $pool#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t10 := coin::value<#0>($t9) on_abort goto L2 with $t8 at ./sources/vault.move:70:26+22
    call $t10 := $2_coin_value'#0'($t9);
    if ($abort_flag) {
        assume {:print "$at(4,2032,2054)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[pool_value#1#0]($t10) at ./sources/vault.move:70:13+10
    assume {:print "$track_local(18,2,4):", $t10} $t10 == $t10;

    // $t11 := 100000000 at ./sources/vault.move:71:32+8
    assume {:print "$at(4,2087,2095)"} true;
    $t11 := 100000000;
    assume $IsValid'u64'($t11);

    // $t12 := *($t10, $t11) on_abort goto L2 with $t8 at ./sources/vault.move:71:30+1
    call $t12 := $Mulu256($t10, $t11);
    if ($abort_flag) {
        assume {:print "$at(4,2085,2086)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t13 := 100000000 at ./sources/vault.move:71:43+11
    $t13 := 100000000;
    assume $IsValid'u64'($t13);

    // $t14 := /($t12, $t13) on_abort goto L2 with $t8 at ./sources/vault.move:71:41+1
    call $t14 := $Div($t12, $t13);
    if ($abort_flag) {
        assume {:print "$at(4,2096,2097)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[amt#1#0]($t14) at ./sources/vault.move:71:13+3
    assume {:print "$track_local(18,2,3):", $t14} $t14 == $t14;

    // debug::print<u64>($t14) on_abort goto L2 with $t8 at ./sources/vault.move:72:9+11
    assume {:print "$at(4,2119,2130)"} true;
    call $1_debug_print'u64'($t14);
    if ($abort_flag) {
        assume {:print "$at(4,2119,2130)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t15 := *($t7, $t14) on_abort goto L2 with $t8 at ./sources/vault.move:74:25+1
    assume {:print "$at(4,2157,2158)"} true;
    call $t15 := $Mulu256($t7, $t14);
    if ($abort_flag) {
        assume {:print "$at(4,2157,2158)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t16 := get_field<vault::Vault<#0, #1>>.lp_supply($t0) at ./sources/vault.move:74:33+13
    $t16 := $lp_supply#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t17 := /($t15, $t16) on_abort goto L2 with $t8 at ./sources/vault.move:74:31+1
    call $t17 := $Div($t15, $t16);
    if ($abort_flag) {
        assume {:print "$at(4,2163,2164)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[ret#1#0]($t17) at ./sources/vault.move:74:13+3
    assume {:print "$track_local(18,2,5):", $t17} $t17 == $t17;

    // debug::print<u64>($t17) on_abort goto L2 with $t8 at ./sources/vault.move:76:9+11
    assume {:print "$at(4,2189,2200)"} true;
    call $1_debug_print'u64'($t17);
    if ($abort_flag) {
        assume {:print "$at(4,2189,2200)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // debug::print<u64>($t10) on_abort goto L2 with $t8 at ./sources/vault.move:77:9+18
    assume {:print "$at(4,2210,2228)"} true;
    call $1_debug_print'u64'($t10);
    if ($abort_flag) {
        assume {:print "$at(4,2210,2228)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t18 := get_field<vault::Vault<#0, #1>>.lp_supply($t0) at ./sources/vault.move:79:25+13
    assume {:print "$at(4,2255,2268)"} true;
    $t18 := $lp_supply#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t19 := -($t18, $t7) on_abort goto L2 with $t8 at ./sources/vault.move:79:39+1
    call $t19 := $Sub($t18, $t7);
    if ($abort_flag) {
        assume {:print "$at(4,2269,2270)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t20 := borrow_field<vault::Vault<#0, #1>>.lp_supply($t0) at ./sources/vault.move:79:9+13
    $t20 := $ChildMutation($t0, 3, $lp_supply#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // write_ref($t20, $t19) at ./sources/vault.move:79:9+37
    $t20 := $UpdateMutation($t20, $t19);

    // write_back[Reference($t0).lp_supply (u64)]($t20) at ./sources/vault.move:79:9+37
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_lp_supply($Dereference($t0), $Dereference($t20)));

    // trace_local[vau]($t0) at ./sources/vault.move:79:9+37
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,2,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // $t21 := borrow_field<vault::Vault<#0, #1>>.lp_valult($t0) at ./sources/vault.move:80:20+18
    assume {:print "$at(4,2297,2315)"} true;
    $t21 := $ChildMutation($t0, 4, $lp_valult#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // assume Identical($t22, select balance::Balance.value(select coin::Coin.balance($t21))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:171:9+36
    assume {:print "$at(29,5814,5850)"} true;
    assume ($t22 == $value#$2_balance_Balance'#1'($balance#$2_coin_Coin'#1'($Dereference($t21))));

    // coin::join<#1>($t21, $t1) on_abort goto L2 with $t8 at ./sources/vault.move:80:9+33
    assume {:print "$at(4,2286,2319)"} true;
    call $t21 := $2_coin_join'#1'($t21, $t1);
    if ($abort_flag) {
        assume {:print "$at(4,2286,2319)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // write_back[Reference($t0).lp_valult (coin::Coin<#1>)]($t21) at ./sources/vault.move:80:9+33
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_lp_valult($Dereference($t0), $Dereference($t21)));

    // trace_local[vau]($t0) at ./sources/vault.move:80:9+33
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,2,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // $t23 := borrow_field<vault::Vault<#0, #1>>.pool($t0) at ./sources/vault.move:82:32+13
    assume {:print "$at(4,2353,2366)"} true;
    $t23 := $ChildMutation($t0, 1, $pool#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // assume Identical($t24, select balance::Balance.value(select coin::Coin.balance($t23))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:187:9+36
    assume {:print "$at(29,6343,6379)"} true;
    assume ($t24 == $value#$2_balance_Balance'#0'($balance#$2_coin_Coin'#0'($Dereference($t23))));

    // $t25 := coin::split<#0>($t23, $t17, $t2) on_abort goto L2 with $t8 at ./sources/vault.move:82:20+36
    assume {:print "$at(4,2341,2377)"} true;
    call $t25,$t23,$t2 := $2_coin_split'#0'($t23, $t17, $t2);
    if ($abort_flag) {
        assume {:print "$at(4,2341,2377)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // write_back[Reference($t0).pool (coin::Coin<#0>)]($t23) at ./sources/vault.move:82:20+36
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_pool($Dereference($t0), $Dereference($t23)));

    // trace_local[vau]($t0) at ./sources/vault.move:82:20+36
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,2,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // $t26 := read_ref($t2) at ./sources/vault.move:83:50+3
    assume {:print "$at(4,2428,2431)"} true;
    $t26 := $Dereference($t2);

    // $t27 := tx_context::sender($t26) on_abort goto L2 with $t8 at ./sources/vault.move:83:31+23
    call $t27 := $2_tx_context_sender($t26);
    if ($abort_flag) {
        assume {:print "$at(4,2409,2432)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // transfer::public_transfer<coin::Coin<#0>>($t25, $t27) on_abort goto L2 with $t8 at ./sources/vault.move:83:9+46
    call $2_transfer_public_transfer'$2_coin_Coin'#0''($t25, $t27);
    if ($abort_flag) {
        assume {:print "$at(4,2387,2433)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[vau]($t0) at ./sources/vault.move:83:9+46
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,2,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[ctx]($t2) at ./sources/vault.move:83:9+46
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(18,2,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./sources/vault.move:84:5+1
    assume {:print "$at(4,2438,2439)"} true;
L1:

    // return () at ./sources/vault.move:84:5+1
    assume {:print "$at(4,2438,2439)"} true;
    $ret0 := $t0;
    $ret1 := $t2;
    return;

    // label L2 at ./sources/vault.move:84:5+1
L2:

    // abort($t8) at ./sources/vault.move:84:5+1
    assume {:print "$at(4,2438,2439)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun vault::win<#0, #1> [baseline] at ./sources/vault.move:86:5+438
procedure {:inline 1} $0_vault_win'#0_#1'(_$t0: $Mutation ($0_vault_Vault'#0_#1'), _$t1: $2_coin_Coin'#0') returns ($ret0: $Mutation ($0_vault_Vault'#0_#1'))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $2_coin_Coin'#0';
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: $Mutation (int);
    var $t19: $0_vault_Vault'#0_#1';
    var $t20: $Mutation ($2_coin_Coin'#0');
    var $t21: int;
    var $t0: $Mutation ($0_vault_Vault'#0_#1');
    var $t1: $2_coin_Coin'#0';
    var $temp_0'$0_vault_Vault'#0_#1'': $0_vault_Vault'#0_#1';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[vau]($t0) at ./sources/vault.move:86:5+1
    assume {:print "$at(4,2445,2446)"} true;
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,3,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[c]($t1) at ./sources/vault.move:86:5+1
    assume {:print "$track_local(18,3,1):", $t1} $t1 == $t1;

    // $t6 := coin::value<#0>($t1) on_abort goto L2 with $t7 at ./sources/vault.move:87:21+15
    assume {:print "$at(4,2527,2542)"} true;
    call $t6 := $2_coin_value'#0'($t1);
    if ($abort_flag) {
        assume {:print "$at(4,2527,2542)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[value#1#0]($t6) at ./sources/vault.move:87:13+5
    assume {:print "$track_local(18,3,5):", $t6} $t6 == $t6;

    // $t8 := get_field<vault::Vault<#0, #1>>.pool($t0) at ./sources/vault.move:89:38+9
    assume {:print "$at(4,2582,2591)"} true;
    $t8 := $pool#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t9 := coin::value<#0>($t8) on_abort goto L2 with $t7 at ./sources/vault.move:89:26+22
    call $t9 := $2_coin_value'#0'($t8);
    if ($abort_flag) {
        assume {:print "$at(4,2570,2592)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[pool_value#1#0]($t9) at ./sources/vault.move:89:13+10
    assume {:print "$track_local(18,3,4):", $t9} $t9 == $t9;

    // $t10 := get_field<vault::Vault<#0, #1>>.lp_price($t0) at ./sources/vault.move:90:30+12
    assume {:print "$at(4,2623,2635)"} true;
    $t10 := $lp_price#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t11 := *($t6, $t10) on_abort goto L2 with $t7 at ./sources/vault.move:90:28+1
    call $t11 := $Mulu256($t6, $t10);
    if ($abort_flag) {
        assume {:print "$at(4,2621,2622)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t12 := 100000000 at ./sources/vault.move:90:45+11
    $t12 := 100000000;
    assume $IsValid'u64'($t12);

    // $t13 := /($t11, $t12) on_abort goto L2 with $t7 at ./sources/vault.move:90:43+1
    call $t13 := $Div($t11, $t12);
    if ($abort_flag) {
        assume {:print "$at(4,2636,2637)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[amount#1#0]($t13) at ./sources/vault.move:90:13+6
    assume {:print "$track_local(18,3,2):", $t13} $t13 == $t13;

    // $t14 := +($t9, $t13) on_abort goto L2 with $t7 at ./sources/vault.move:92:37+1
    assume {:print "$at(4,2688,2689)"} true;
    call $t14 := $Addu256($t9, $t13);
    if ($abort_flag) {
        assume {:print "$at(4,2688,2689)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t15 := 100000000 at ./sources/vault.move:93:37+11
    assume {:print "$at(4,2734,2745)"} true;
    $t15 := 100000000;
    assume $IsValid'u64'($t15);

    // $t16 := *($t14, $t15) on_abort goto L2 with $t7 at ./sources/vault.move:93:35+1
    call $t16 := $Mulu256($t14, $t15);
    if ($abort_flag) {
        assume {:print "$at(4,2732,2733)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t17 := /($t16, $t9) on_abort goto L2 with $t7 at ./sources/vault.move:93:49+1
    call $t17 := $Div($t16, $t9);
    if ($abort_flag) {
        assume {:print "$at(4,2746,2747)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[lp_price#1#0]($t17) at ./sources/vault.move:93:13+8
    assume {:print "$track_local(18,3,3):", $t17} $t17 == $t17;

    // $t18 := borrow_field<vault::Vault<#0, #1>>.lp_price($t0) at ./sources/vault.move:94:9+12
    assume {:print "$at(4,2768,2780)"} true;
    $t18 := $ChildMutation($t0, 2, $lp_price#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // write_ref($t18, $t17) at ./sources/vault.move:94:9+23
    $t18 := $UpdateMutation($t18, $t17);

    // write_back[Reference($t0).lp_price (u64)]($t18) at ./sources/vault.move:94:9+23
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_lp_price($Dereference($t0), $Dereference($t18)));

    // trace_local[vau]($t0) at ./sources/vault.move:94:9+23
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,3,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // debug::print<u64>($t17) on_abort goto L2 with $t7 at ./sources/vault.move:96:9+16
    assume {:print "$at(4,2802,2818)"} true;
    call $1_debug_print'u64'($t17);
    if ($abort_flag) {
        assume {:print "$at(4,2802,2818)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t19 := read_ref($t0) at ./sources/vault.move:97:15+3
    assume {:print "$at(4,2834,2837)"} true;
    $t19 := $Dereference($t0);

    // debug::print<vault::Vault<#0, #1>>($t19) on_abort goto L2 with $t7 at ./sources/vault.move:97:9+10
    call $1_debug_print'$0_vault_Vault'#0_#1''($t19);
    if ($abort_flag) {
        assume {:print "$at(4,2828,2838)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t20 := borrow_field<vault::Vault<#0, #1>>.pool($t0) at ./sources/vault.move:98:20+13
    assume {:print "$at(4,2859,2872)"} true;
    $t20 := $ChildMutation($t0, 1, $pool#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // assume Identical($t21, select balance::Balance.value(select coin::Coin.balance($t20))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:171:9+36
    assume {:print "$at(29,5814,5850)"} true;
    assume ($t21 == $value#$2_balance_Balance'#0'($balance#$2_coin_Coin'#0'($Dereference($t20))));

    // coin::join<#0>($t20, $t1) on_abort goto L2 with $t7 at ./sources/vault.move:98:9+28
    assume {:print "$at(4,2848,2876)"} true;
    call $t20 := $2_coin_join'#0'($t20, $t1);
    if ($abort_flag) {
        assume {:print "$at(4,2848,2876)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // write_back[Reference($t0).pool (coin::Coin<#0>)]($t20) at ./sources/vault.move:98:9+28
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_pool($Dereference($t0), $Dereference($t20)));

    // trace_local[vau]($t0) at ./sources/vault.move:98:9+28
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,3,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[vau]($t0) at ./sources/vault.move:98:37+1
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,3,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // label L1 at ./sources/vault.move:99:5+1
    assume {:print "$at(4,2882,2883)"} true;
L1:

    // return () at ./sources/vault.move:99:5+1
    assume {:print "$at(4,2882,2883)"} true;
    $ret0 := $t0;
    return;

    // label L2 at ./sources/vault.move:99:5+1
L2:

    // abort($t7) at ./sources/vault.move:99:5+1
    assume {:print "$at(4,2882,2883)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun vault::win [verification] at ./sources/vault.move:86:5+438
procedure {:timeLimit 40} $0_vault_win$verify(_$t0: $Mutation ($0_vault_Vault'#0_#1'), _$t1: $2_coin_Coin'#0') returns ($ret0: $Mutation ($0_vault_Vault'#0_#1'))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $2_coin_Coin'#0';
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: $Mutation (int);
    var $t19: $0_vault_Vault'#0_#1';
    var $t20: $Mutation ($2_coin_Coin'#0');
    var $t21: int;
    var $t0: $Mutation ($0_vault_Vault'#0_#1');
    var $t1: $2_coin_Coin'#0';
    var $temp_0'$0_vault_Vault'#0_#1'': $0_vault_Vault'#0_#1';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/vault.move:86:5+1
    assume {:print "$at(4,2445,2446)"} true;
    assume $IsValid'$0_vault_Vault'#0_#1''($Dereference($t0));

    // assume WellFormed($t1) at ./sources/vault.move:86:5+1
    assume $IsValid'$2_coin_Coin'#0''($t1);

    // trace_local[vau]($t0) at ./sources/vault.move:86:5+1
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,3,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[c]($t1) at ./sources/vault.move:86:5+1
    assume {:print "$track_local(18,3,1):", $t1} $t1 == $t1;

    // $t6 := coin::value<#0>($t1) on_abort goto L2 with $t7 at ./sources/vault.move:87:21+15
    assume {:print "$at(4,2527,2542)"} true;
    call $t6 := $2_coin_value'#0'($t1);
    if ($abort_flag) {
        assume {:print "$at(4,2527,2542)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[value#1#0]($t6) at ./sources/vault.move:87:13+5
    assume {:print "$track_local(18,3,5):", $t6} $t6 == $t6;

    // $t8 := get_field<vault::Vault<#0, #1>>.pool($t0) at ./sources/vault.move:89:38+9
    assume {:print "$at(4,2582,2591)"} true;
    $t8 := $pool#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t9 := coin::value<#0>($t8) on_abort goto L2 with $t7 at ./sources/vault.move:89:26+22
    call $t9 := $2_coin_value'#0'($t8);
    if ($abort_flag) {
        assume {:print "$at(4,2570,2592)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[pool_value#1#0]($t9) at ./sources/vault.move:89:13+10
    assume {:print "$track_local(18,3,4):", $t9} $t9 == $t9;

    // $t10 := get_field<vault::Vault<#0, #1>>.lp_price($t0) at ./sources/vault.move:90:30+12
    assume {:print "$at(4,2623,2635)"} true;
    $t10 := $lp_price#$0_vault_Vault'#0_#1'($Dereference($t0));

    // $t11 := *($t6, $t10) on_abort goto L2 with $t7 at ./sources/vault.move:90:28+1
    call $t11 := $Mulu256($t6, $t10);
    if ($abort_flag) {
        assume {:print "$at(4,2621,2622)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t12 := 100000000 at ./sources/vault.move:90:45+11
    $t12 := 100000000;
    assume $IsValid'u64'($t12);

    // $t13 := /($t11, $t12) on_abort goto L2 with $t7 at ./sources/vault.move:90:43+1
    call $t13 := $Div($t11, $t12);
    if ($abort_flag) {
        assume {:print "$at(4,2636,2637)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[amount#1#0]($t13) at ./sources/vault.move:90:13+6
    assume {:print "$track_local(18,3,2):", $t13} $t13 == $t13;

    // $t14 := +($t9, $t13) on_abort goto L2 with $t7 at ./sources/vault.move:92:37+1
    assume {:print "$at(4,2688,2689)"} true;
    call $t14 := $Addu256($t9, $t13);
    if ($abort_flag) {
        assume {:print "$at(4,2688,2689)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t15 := 100000000 at ./sources/vault.move:93:37+11
    assume {:print "$at(4,2734,2745)"} true;
    $t15 := 100000000;
    assume $IsValid'u64'($t15);

    // $t16 := *($t14, $t15) on_abort goto L2 with $t7 at ./sources/vault.move:93:35+1
    call $t16 := $Mulu256($t14, $t15);
    if ($abort_flag) {
        assume {:print "$at(4,2732,2733)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t17 := /($t16, $t9) on_abort goto L2 with $t7 at ./sources/vault.move:93:49+1
    call $t17 := $Div($t16, $t9);
    if ($abort_flag) {
        assume {:print "$at(4,2746,2747)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[lp_price#1#0]($t17) at ./sources/vault.move:93:13+8
    assume {:print "$track_local(18,3,3):", $t17} $t17 == $t17;

    // $t18 := borrow_field<vault::Vault<#0, #1>>.lp_price($t0) at ./sources/vault.move:94:9+12
    assume {:print "$at(4,2768,2780)"} true;
    $t18 := $ChildMutation($t0, 2, $lp_price#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // write_ref($t18, $t17) at ./sources/vault.move:94:9+23
    $t18 := $UpdateMutation($t18, $t17);

    // write_back[Reference($t0).lp_price (u64)]($t18) at ./sources/vault.move:94:9+23
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_lp_price($Dereference($t0), $Dereference($t18)));

    // trace_local[vau]($t0) at ./sources/vault.move:94:9+23
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,3,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // debug::print<u64>($t17) on_abort goto L2 with $t7 at ./sources/vault.move:96:9+16
    assume {:print "$at(4,2802,2818)"} true;
    call $1_debug_print'u64'($t17);
    if ($abort_flag) {
        assume {:print "$at(4,2802,2818)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t19 := read_ref($t0) at ./sources/vault.move:97:15+3
    assume {:print "$at(4,2834,2837)"} true;
    $t19 := $Dereference($t0);

    // debug::print<vault::Vault<#0, #1>>($t19) on_abort goto L2 with $t7 at ./sources/vault.move:97:9+10
    call $1_debug_print'$0_vault_Vault'#0_#1''($t19);
    if ($abort_flag) {
        assume {:print "$at(4,2828,2838)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t20 := borrow_field<vault::Vault<#0, #1>>.pool($t0) at ./sources/vault.move:98:20+13
    assume {:print "$at(4,2859,2872)"} true;
    $t20 := $ChildMutation($t0, 1, $pool#$0_vault_Vault'#0_#1'($Dereference($t0)));

    // assume Identical($t21, select balance::Balance.value(select coin::Coin.balance($t20))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:171:9+36
    assume {:print "$at(29,5814,5850)"} true;
    assume ($t21 == $value#$2_balance_Balance'#0'($balance#$2_coin_Coin'#0'($Dereference($t20))));

    // coin::join<#0>($t20, $t1) on_abort goto L2 with $t7 at ./sources/vault.move:98:9+28
    assume {:print "$at(4,2848,2876)"} true;
    call $t20 := $2_coin_join'#0'($t20, $t1);
    if ($abort_flag) {
        assume {:print "$at(4,2848,2876)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // write_back[Reference($t0).pool (coin::Coin<#0>)]($t20) at ./sources/vault.move:98:9+28
    $t0 := $UpdateMutation($t0, $Update'$0_vault_Vault'#0_#1''_pool($Dereference($t0), $Dereference($t20)));

    // trace_local[vau]($t0) at ./sources/vault.move:98:9+28
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,3,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[vau]($t0) at ./sources/vault.move:98:37+1
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(18,3,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // label L1 at ./sources/vault.move:99:5+1
    assume {:print "$at(4,2882,2883)"} true;
L1:

    // return () at ./sources/vault.move:99:5+1
    assume {:print "$at(4,2882,2883)"} true;
    $ret0 := $t0;
    return;

    // label L2 at ./sources/vault.move:99:5+1
L2:

    // abort($t7) at ./sources/vault.move:99:5+1
    assume {:print "$at(4,2882,2883)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun bcs::to_bytes<tx_context::TxContext> [baseline] at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/bcs.move:59:5+82
procedure {:inline 1} $2_bcs_to_bytes'$2_tx_context_TxContext'(_$t0: $2_tx_context_TxContext) returns ($ret0: Vec (int))
{
    // declare local variables
    var $t1: Vec (int);
    var $t2: int;
    var $t0: $2_tx_context_TxContext;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[value]($t0) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/bcs.move:59:5+1
    assume {:print "$at(26,1819,1820)"} true;
    assume {:print "$track_local(19,0,0):", $t0} $t0 == $t0;

    // $t1 := bcs::to_bytes<#0>($t0) on_abort goto L2 with $t2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/bcs.move:60:9+20
    assume {:print "$at(26,1875,1895)"} true;
    call $t1 := $1_bcs_to_bytes'$2_tx_context_TxContext'($t0);
    if ($abort_flag) {
        assume {:print "$at(26,1875,1895)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(19,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/bcs.move:60:9+20
    assume {:print "$track_return(19,0,0):", $t1} $t1 == $t1;

    // label L1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/bcs.move:61:5+1
    assume {:print "$at(26,1900,1901)"} true;
L1:

    // return $t1 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/bcs.move:61:5+1
    assume {:print "$at(26,1900,1901)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/bcs.move:61:5+1
L2:

    // abort($t2) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/bcs.move:61:5+1
    assume {:print "$at(26,1900,1901)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun random::bytes_to_u256 [baseline] at ./sources/random.move:25:5+267
procedure {:inline 1} $0_random_bytes_to_u256(_$t0: Vec (int)) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: bv64;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t0: Vec (int);
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[bytes]($t0) at ./sources/random.move:25:5+1
    assume {:print "$at(3,649,650)"} true;
    assume {:print "$track_local(21,1,0):", $t0} $t0 == $t0;

    // $t3 := 0 at ./sources/random.move:26:21+4
    assume {:print "$at(3,712,716)"} true;
    $t3 := 0;
    assume $IsValid'u64'($t3);

    // trace_local[value#1#0]($t3) at ./sources/random.move:26:13+5
    assume {:print "$track_local(21,1,2):", $t3} $t3 == $t3;

    // $t4 := 0 at ./sources/random.move:27:17+4
    assume {:print "$at(3,734,738)"} true;
    $t4 := 0;
    assume $IsValid'u64'($t4);

    // trace_local[i#1#0]($t4) at ./sources/random.move:27:13+1
    assume {:print "$track_local(21,1,1):", $t4} $t4 == $t4;

    // label L3 at ./sources/random.move:28:16+1
    assume {:print "$at(3,755,756)"} true;
L3:

    // $t1 := havoc[val]() at ./sources/random.move:28:16+1
    assume {:print "$at(3,755,756)"} true;
    havoc $t1;

    // assume WellFormed($t1) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t1);

    // $t2 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t2;

    // assume WellFormed($t2) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t2);

    // $t5 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t5;

    // assume WellFormed($t5) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t5);

    // $t6 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t6;

    // assume WellFormed($t6) at ./sources/random.move:28:16+1
    assume $IsValid'bool'($t6);

    // $t7 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t7;

    // assume WellFormed($t7) at ./sources/random.move:28:16+1
    assume $IsValid'u8'($t7);

    // $t8 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t8;

    // assume WellFormed($t8) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t8);

    // $t9 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t9;

    // assume WellFormed($t9) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t9);

    // $t10 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t10;

    // assume WellFormed($t10) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t10);

    // $t11 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t11;

    // assume WellFormed($t11) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t11);

    // $t12 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t12;

    // assume WellFormed($t12) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t12);

    // $t13 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t13;

    // assume WellFormed($t13) at ./sources/random.move:28:16+1
    assume $IsValid'u8'($t13);

    // $t14 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t14;

    // assume WellFormed($t14) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t14);

    // $t15 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t15;

    // assume WellFormed($t15) at ./sources/random.move:28:16+1
    assume $IsValid'bv64'($t15);

    // $t16 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t16;

    // assume WellFormed($t16) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t16);

    // $t17 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t17;

    // assume WellFormed($t17) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t17);

    // trace_local[i#1#0]($t1) at ./sources/random.move:28:16+1
    assume {:print "$info(): enter loop, variable(s) i#1#0, value#1#0 havocked and reassigned"} true;
    assume {:print "$track_local(21,1,1):", $t1} $t1 == $t1;

    // trace_local[value#1#0]($t2) at ./sources/random.move:28:16+1
    assume {:print "$track_local(21,1,2):", $t2} $t2 == $t2;

    // assume Not(AbortFlag()) at ./sources/random.move:28:16+1
    assume !$abort_flag;

    // $t5 := 8 at ./sources/random.move:28:20+1
    $t5 := 8;
    assume $IsValid'u64'($t5);

    // $t6 := <($t1, $t5) at ./sources/random.move:28:18+1
    call $t6 := $Lt($t1, $t5);

    // if ($t6) goto L1 else goto L0 at ./sources/random.move:28:9+140
    if ($t6) { goto L1; } else { goto L0; }

    // label L1 at ./sources/random.move:28:9+140
L1:

    // label L2 at ./sources/random.move:29:21+5
    assume {:print "$at(3,784,789)"} true;
L2:

    // $t7 := vector::borrow<u8>($t0, $t1) on_abort goto L6 with $t18 at ./sources/random.move:29:32+25
    assume {:print "$at(3,795,820)"} true;
    call $t7 := $1_vector_borrow'u8'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,795,820)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // $t8 := (u64)($t7) on_abort goto L6 with $t18 at ./sources/random.move:29:30+35
    call $t8 := $Castu256($t7);
    if ($abort_flag) {
        assume {:print "$at(3,793,828)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // $t9 := 8 at ./sources/random.move:29:71+1
    $t9 := 8;
    assume $IsValid'u64'($t9);

    // $t10 := 7 at ./sources/random.move:29:76+1
    $t10 := 7;
    assume $IsValid'u64'($t10);

    // $t11 := -($t10, $t1) on_abort goto L6 with $t18 at ./sources/random.move:29:78+1
    call $t11 := $Sub($t10, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,841,842)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // $t12 := *($t9, $t11) on_abort goto L6 with $t18 at ./sources/random.move:29:73+1
    call $t12 := $Mulu256($t9, $t11);
    if ($abort_flag) {
        assume {:print "$at(3,836,837)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // $t13 := (u8)($t12) on_abort goto L6 with $t18 at ./sources/random.move:29:69+21
    call $t13 := $CastU8($t12);
    if ($abort_flag) {
        assume {:print "$at(3,832,853)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // $t14 := <<($t8, $t13) on_abort goto L6 with $t18 at ./sources/random.move:29:66+2
    call $t14 := $Shlu256($t8, $t13);
    if ($abort_flag) {
        assume {:print "$at(3,829,831)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // $t15 := |($t2, $t14) at ./sources/random.move:29:27+1
    call $t15 := $OrBv64($int2bv.64($t2), $int2bv.64($t14));

    // trace_local[value#1#0]($t15) at ./sources/random.move:29:13+5
    assume {:print "$track_local(21,1,2):", $t15} $t15 == $t15;

    // $t16 := 1 at ./sources/random.move:30:21+1
    assume {:print "$at(3,876,877)"} true;
    $t16 := 1;
    assume $IsValid'u64'($t16);

    // $t17 := +($t1, $t16) on_abort goto L6 with $t18 at ./sources/random.move:30:19+1
    call $t17 := $Addu256($t1, $t16);
    if ($abort_flag) {
        assume {:print "$at(3,874,875)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // trace_local[i#1#0]($t17) at ./sources/random.move:30:13+1
    assume {:print "$track_local(21,1,1):", $t17} $t17 == $t17;

    // goto L4 at ./sources/random.move:30:22+1
    goto L4;

    // label L0 at ./sources/random.move:32:16+5
    assume {:print "$at(3,905,910)"} true;
L0:

    // trace_return[0]($t2) at ./sources/random.move:32:9+12
    assume {:print "$at(3,898,910)"} true;
    assume {:print "$track_return(21,1,0):", $t2} $t2 == $t2;

    // $t19 := move($t2) at ./sources/random.move:32:9+12
    $t19 := $t2;

    // goto L5 at ./sources/random.move:32:9+12
    goto L5;

    // label L4 at ./sources/random.move:32:16+5
    // Loop invariant checking block for the loop started with header: L3
L4:

    // stop() at ./sources/random.move:32:16+5
    assume {:print "$at(3,905,910)"} true;
    assume false;
    return;

    // label L5 at ./sources/random.move:33:5+1
    assume {:print "$at(3,915,916)"} true;
L5:

    // return $t19 at ./sources/random.move:33:5+1
    assume {:print "$at(3,915,916)"} true;
    $ret0 := $t19;
    return;

    // label L6 at ./sources/random.move:33:5+1
L6:

    // abort($t18) at ./sources/random.move:33:5+1
    assume {:print "$at(3,915,916)"} true;
    $abort_code := $t18;
    $abort_flag := true;
    return;

}

// fun random::bytes_to_u256 [verification] at ./sources/random.move:25:5+267
procedure {:timeLimit 40} $0_random_bytes_to_u256$verify(_$t0: Vec (int)) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: bv64;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t0: Vec (int);
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/random.move:25:5+1
    assume {:print "$at(3,649,650)"} true;
    assume $IsValid'vec'u8''($t0);

    // trace_local[bytes]($t0) at ./sources/random.move:25:5+1
    assume {:print "$track_local(21,1,0):", $t0} $t0 == $t0;

    // $t3 := 0 at ./sources/random.move:26:21+4
    assume {:print "$at(3,712,716)"} true;
    $t3 := 0;
    assume $IsValid'u64'($t3);

    // trace_local[value#1#0]($t3) at ./sources/random.move:26:13+5
    assume {:print "$track_local(21,1,2):", $t3} $t3 == $t3;

    // $t4 := 0 at ./sources/random.move:27:17+4
    assume {:print "$at(3,734,738)"} true;
    $t4 := 0;
    assume $IsValid'u64'($t4);

    // trace_local[i#1#0]($t4) at ./sources/random.move:27:13+1
    assume {:print "$track_local(21,1,1):", $t4} $t4 == $t4;

    // label L3 at ./sources/random.move:28:16+1
    assume {:print "$at(3,755,756)"} true;
L3:

    // $t1 := havoc[val]() at ./sources/random.move:28:16+1
    assume {:print "$at(3,755,756)"} true;
    havoc $t1;

    // assume WellFormed($t1) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t1);

    // $t2 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t2;

    // assume WellFormed($t2) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t2);

    // $t5 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t5;

    // assume WellFormed($t5) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t5);

    // $t6 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t6;

    // assume WellFormed($t6) at ./sources/random.move:28:16+1
    assume $IsValid'bool'($t6);

    // $t7 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t7;

    // assume WellFormed($t7) at ./sources/random.move:28:16+1
    assume $IsValid'u8'($t7);

    // $t8 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t8;

    // assume WellFormed($t8) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t8);

    // $t9 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t9;

    // assume WellFormed($t9) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t9);

    // $t10 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t10;

    // assume WellFormed($t10) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t10);

    // $t11 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t11;

    // assume WellFormed($t11) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t11);

    // $t12 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t12;

    // assume WellFormed($t12) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t12);

    // $t13 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t13;

    // assume WellFormed($t13) at ./sources/random.move:28:16+1
    assume $IsValid'u8'($t13);

    // $t14 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t14;

    // assume WellFormed($t14) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t14);

    // $t15 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t15;

    // assume WellFormed($t15) at ./sources/random.move:28:16+1
    assume $IsValid'bv64'($t15);

    // $t16 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t16;

    // assume WellFormed($t16) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t16);

    // $t17 := havoc[val]() at ./sources/random.move:28:16+1
    havoc $t17;

    // assume WellFormed($t17) at ./sources/random.move:28:16+1
    assume $IsValid'u64'($t17);

    // trace_local[i#1#0]($t1) at ./sources/random.move:28:16+1
    assume {:print "$info(): enter loop, variable(s) i#1#0, value#1#0 havocked and reassigned"} true;
    assume {:print "$track_local(21,1,1):", $t1} $t1 == $t1;

    // trace_local[value#1#0]($t2) at ./sources/random.move:28:16+1
    assume {:print "$track_local(21,1,2):", $t2} $t2 == $t2;

    // assume Not(AbortFlag()) at ./sources/random.move:28:16+1
    assume !$abort_flag;

    // $t5 := 8 at ./sources/random.move:28:20+1
    $t5 := 8;
    assume $IsValid'u64'($t5);

    // $t6 := <($t1, $t5) at ./sources/random.move:28:18+1
    call $t6 := $Lt($t1, $t5);

    // if ($t6) goto L1 else goto L0 at ./sources/random.move:28:9+140
    if ($t6) { goto L1; } else { goto L0; }

    // label L1 at ./sources/random.move:28:9+140
L1:

    // label L2 at ./sources/random.move:29:21+5
    assume {:print "$at(3,784,789)"} true;
L2:

    // $t7 := vector::borrow<u8>($t0, $t1) on_abort goto L6 with $t18 at ./sources/random.move:29:32+25
    assume {:print "$at(3,795,820)"} true;
    call $t7 := $1_vector_borrow'u8'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,795,820)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // $t8 := (u64)($t7) on_abort goto L6 with $t18 at ./sources/random.move:29:30+35
    call $t8 := $Castu256($t7);
    if ($abort_flag) {
        assume {:print "$at(3,793,828)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // $t9 := 8 at ./sources/random.move:29:71+1
    $t9 := 8;
    assume $IsValid'u64'($t9);

    // $t10 := 7 at ./sources/random.move:29:76+1
    $t10 := 7;
    assume $IsValid'u64'($t10);

    // $t11 := -($t10, $t1) on_abort goto L6 with $t18 at ./sources/random.move:29:78+1
    call $t11 := $Sub($t10, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,841,842)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // $t12 := *($t9, $t11) on_abort goto L6 with $t18 at ./sources/random.move:29:73+1
    call $t12 := $Mulu256($t9, $t11);
    if ($abort_flag) {
        assume {:print "$at(3,836,837)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // $t13 := (u8)($t12) on_abort goto L6 with $t18 at ./sources/random.move:29:69+21
    call $t13 := $CastU8($t12);
    if ($abort_flag) {
        assume {:print "$at(3,832,853)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // $t14 := <<($t8, $t13) on_abort goto L6 with $t18 at ./sources/random.move:29:66+2
    call $t14 := $Shlu256($t8, $t13);
    if ($abort_flag) {
        assume {:print "$at(3,829,831)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // $t15 := |($t2, $t14) at ./sources/random.move:29:27+1
    call $t15 := $OrBv64($int2bv.64($t2), $int2bv.64($t14));

    // trace_local[value#1#0]($t15) at ./sources/random.move:29:13+5
    assume {:print "$track_local(21,1,2):", $t15} $t15 == $t15;

    // $t16 := 1 at ./sources/random.move:30:21+1
    assume {:print "$at(3,876,877)"} true;
    $t16 := 1;
    assume $IsValid'u64'($t16);

    // $t17 := +($t1, $t16) on_abort goto L6 with $t18 at ./sources/random.move:30:19+1
    call $t17 := $Addu256($t1, $t16);
    if ($abort_flag) {
        assume {:print "$at(3,874,875)"} true;
        $t18 := $abort_code;
        assume {:print "$track_abort(21,1):", $t18} $t18 == $t18;
        goto L6;
    }

    // trace_local[i#1#0]($t17) at ./sources/random.move:30:13+1
    assume {:print "$track_local(21,1,1):", $t17} $t17 == $t17;

    // goto L4 at ./sources/random.move:30:22+1
    goto L4;

    // label L0 at ./sources/random.move:32:16+5
    assume {:print "$at(3,905,910)"} true;
L0:

    // trace_return[0]($t2) at ./sources/random.move:32:9+12
    assume {:print "$at(3,898,910)"} true;
    assume {:print "$track_return(21,1,0):", $t2} $t2 == $t2;

    // $t19 := move($t2) at ./sources/random.move:32:9+12
    $t19 := $t2;

    // goto L5 at ./sources/random.move:32:9+12
    goto L5;

    // label L4 at ./sources/random.move:32:16+5
    // Loop invariant checking block for the loop started with header: L3
L4:

    // stop() at ./sources/random.move:32:16+5
    assume {:print "$at(3,905,910)"} true;
    assume false;
    return;

    // label L5 at ./sources/random.move:33:5+1
    assume {:print "$at(3,915,916)"} true;
L5:

    // return $t19 at ./sources/random.move:33:5+1
    assume {:print "$at(3,915,916)"} true;
    $ret0 := $t19;
    return;

    // label L6 at ./sources/random.move:33:5+1
L6:

    // abort($t18) at ./sources/random.move:33:5+1
    assume {:print "$at(3,915,916)"} true;
    $abort_code := $t18;
    $abort_flag := true;
    return;

}

// fun random::rand_u256 [verification] at ./sources/random.move:48:5+91
procedure {:timeLimit 40} $0_random_rand_u256$verify(_$t0: $Mutation ($2_tx_context_TxContext)) returns ($ret0: int, $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t1: Vec (int);
    var $t2: int;
    var $t3: int;
    var $t0: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/random.move:48:5+1
    assume {:print "$at(3,1361,1362)"} true;
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t0));

    // trace_local[ctx]($t0) at ./sources/random.move:48:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(21,4,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t1 := random::seed($t0) on_abort goto L2 with $t2 at ./sources/random.move:49:28+9
    assume {:print "$at(3,1436,1445)"} true;
    call $t1,$t0 := $0_random_seed($t0);
    if ($abort_flag) {
        assume {:print "$at(3,1436,1445)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(21,4):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := random::rand_u256_with_seed($t1) on_abort goto L2 with $t2 at ./sources/random.move:49:9+29
    call $t3 := $0_random_rand_u256_with_seed($t1);
    if ($abort_flag) {
        assume {:print "$at(3,1417,1446)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(21,4):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t3) at ./sources/random.move:49:9+29
    assume {:print "$track_return(21,4,0):", $t3} $t3 == $t3;

    // trace_local[ctx]($t0) at ./sources/random.move:49:9+29
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(21,4,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./sources/random.move:50:5+1
    assume {:print "$at(3,1451,1452)"} true;
L1:

    // return $t3 at ./sources/random.move:50:5+1
    assume {:print "$at(3,1451,1452)"} true;
    $ret0 := $t3;
    $ret1 := $t0;
    return;

    // label L2 at ./sources/random.move:50:5+1
L2:

    // abort($t2) at ./sources/random.move:50:5+1
    assume {:print "$at(3,1451,1452)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun random::rand_u256_range [baseline] at ./sources/random.move:53:5+135
procedure {:inline 1} $0_random_rand_u256_range(_$t0: int, _$t1: int, _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: int, $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: Vec (int);
    var $t4: int;
    var $t5: int;
    var $t0: int;
    var $t1: int;
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[low]($t0) at ./sources/random.move:53:5+1
    assume {:print "$at(3,1514,1515)"} true;
    assume {:print "$track_local(21,5,0):", $t0} $t0 == $t0;

    // trace_local[high]($t1) at ./sources/random.move:53:5+1
    assume {:print "$track_local(21,5,1):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at ./sources/random.move:53:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(21,5,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t3 := random::seed($t2) on_abort goto L2 with $t4 at ./sources/random.move:54:34+9
    assume {:print "$at(3,1622,1631)"} true;
    call $t3,$t2 := $0_random_seed($t2);
    if ($abort_flag) {
        assume {:print "$at(3,1622,1631)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(21,5):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := random::rand_u256_range_with_seed($t3, $t0, $t1) on_abort goto L2 with $t4 at ./sources/random.move:54:9+46
    call $t5 := $0_random_rand_u256_range_with_seed($t3, $t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,1597,1643)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(21,5):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t5) at ./sources/random.move:54:9+46
    assume {:print "$track_return(21,5,0):", $t5} $t5 == $t5;

    // trace_local[ctx]($t2) at ./sources/random.move:54:9+46
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(21,5,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./sources/random.move:55:5+1
    assume {:print "$at(3,1648,1649)"} true;
L1:

    // return $t5 at ./sources/random.move:55:5+1
    assume {:print "$at(3,1648,1649)"} true;
    $ret0 := $t5;
    $ret1 := $t2;
    return;

    // label L2 at ./sources/random.move:55:5+1
L2:

    // abort($t4) at ./sources/random.move:55:5+1
    assume {:print "$at(3,1648,1649)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun random::rand_u256_range [verification] at ./sources/random.move:53:5+135
procedure {:timeLimit 40} $0_random_rand_u256_range$verify(_$t0: int, _$t1: int, _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: int, $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: Vec (int);
    var $t4: int;
    var $t5: int;
    var $t0: int;
    var $t1: int;
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t2) == $Param(2);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/random.move:53:5+1
    assume {:print "$at(3,1514,1515)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at ./sources/random.move:53:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at ./sources/random.move:53:5+1
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t2));

    // trace_local[low]($t0) at ./sources/random.move:53:5+1
    assume {:print "$track_local(21,5,0):", $t0} $t0 == $t0;

    // trace_local[high]($t1) at ./sources/random.move:53:5+1
    assume {:print "$track_local(21,5,1):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at ./sources/random.move:53:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(21,5,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t3 := random::seed($t2) on_abort goto L2 with $t4 at ./sources/random.move:54:34+9
    assume {:print "$at(3,1622,1631)"} true;
    call $t3,$t2 := $0_random_seed($t2);
    if ($abort_flag) {
        assume {:print "$at(3,1622,1631)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(21,5):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := random::rand_u256_range_with_seed($t3, $t0, $t1) on_abort goto L2 with $t4 at ./sources/random.move:54:9+46
    call $t5 := $0_random_rand_u256_range_with_seed($t3, $t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,1597,1643)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(21,5):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t5) at ./sources/random.move:54:9+46
    assume {:print "$track_return(21,5,0):", $t5} $t5 == $t5;

    // trace_local[ctx]($t2) at ./sources/random.move:54:9+46
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(21,5,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./sources/random.move:55:5+1
    assume {:print "$at(3,1648,1649)"} true;
L1:

    // return $t5 at ./sources/random.move:55:5+1
    assume {:print "$at(3,1648,1649)"} true;
    $ret0 := $t5;
    $ret1 := $t2;
    return;

    // label L2 at ./sources/random.move:55:5+1
L2:

    // abort($t4) at ./sources/random.move:55:5+1
    assume {:print "$at(3,1648,1649)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun random::rand_u256_range_with_seed [baseline] at ./sources/random.move:41:5+229
procedure {:inline 1} $0_random_rand_u256_range_with_seed(_$t0: Vec (int), _$t1: int, _$t2: int) returns ($ret0: int)
{
    // declare local variables
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t0: Vec (int);
    var $t1: int;
    var $t2: int;
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[_seed]($t0) at ./sources/random.move:41:5+1
    assume {:print "$at(3,1096,1097)"} true;
    assume {:print "$track_local(21,3,0):", $t0} $t0 == $t0;

    // trace_local[low]($t1) at ./sources/random.move:41:5+1
    assume {:print "$track_local(21,3,1):", $t1} $t1 == $t1;

    // trace_local[high]($t2) at ./sources/random.move:41:5+1
    assume {:print "$track_local(21,3,2):", $t2} $t2 == $t2;

    // $t3 := >($t2, $t1) at ./sources/random.move:42:22+1
    assume {:print "$at(3,1193,1194)"} true;
    call $t3 := $Gt($t2, $t1);

    // if ($t3) goto L1 else goto L0 at ./sources/random.move:42:9+54
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at ./sources/random.move:42:9+54
L1:

    // goto L2 at ./sources/random.move:42:9+54
    assume {:print "$at(3,1180,1234)"} true;
    goto L2;

    // label L0 at ./sources/random.move:42:29+33
L0:

    // $t4 := 101 at ./sources/random.move:42:29+33
    assume {:print "$at(3,1200,1233)"} true;
    $t4 := 101;
    assume $IsValid'u64'($t4);

    // trace_abort($t4) at ./sources/random.move:42:9+54
    assume {:print "$at(3,1180,1234)"} true;
    assume {:print "$track_abort(21,3):", $t4} $t4 == $t4;

    // $t5 := move($t4) at ./sources/random.move:42:9+54
    $t5 := $t4;

    // goto L4 at ./sources/random.move:42:9+54
    goto L4;

    // label L2 at ./sources/random.move:43:40+5
    assume {:print "$at(3,1275,1280)"} true;
L2:

    // $t6 := random::rand_u256_with_seed($t0) on_abort goto L4 with $t5 at ./sources/random.move:43:21+25
    assume {:print "$at(3,1256,1281)"} true;
    call $t6 := $0_random_rand_u256_with_seed($t0);
    if ($abort_flag) {
        assume {:print "$at(3,1256,1281)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(21,3):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t7 := -($t2, $t1) on_abort goto L4 with $t5 at ./sources/random.move:44:24+1
    assume {:print "$at(3,1306,1307)"} true;
    call $t7 := $Sub($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,1306,1307)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(21,3):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t8 := %($t6, $t7) on_abort goto L4 with $t5 at ./sources/random.move:44:16+1
    call $t8 := $Mod($t6, $t7);
    if ($abort_flag) {
        assume {:print "$at(3,1298,1299)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(21,3):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t9 := +($t8, $t1) on_abort goto L4 with $t5 at ./sources/random.move:44:32+1
    call $t9 := $Addu256($t8, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,1314,1315)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(21,3):", $t5} $t5 == $t5;
        goto L4;
    }

    // trace_return[0]($t9) at ./sources/random.move:44:9+28
    assume {:print "$track_return(21,3,0):", $t9} $t9 == $t9;

    // label L3 at ./sources/random.move:45:5+1
    assume {:print "$at(3,1324,1325)"} true;
L3:

    // return $t9 at ./sources/random.move:45:5+1
    assume {:print "$at(3,1324,1325)"} true;
    $ret0 := $t9;
    return;

    // label L4 at ./sources/random.move:45:5+1
L4:

    // abort($t5) at ./sources/random.move:45:5+1
    assume {:print "$at(3,1324,1325)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun random::rand_u256_range_with_seed [verification] at ./sources/random.move:41:5+229
procedure {:timeLimit 40} $0_random_rand_u256_range_with_seed$verify(_$t0: Vec (int), _$t1: int, _$t2: int) returns ($ret0: int)
{
    // declare local variables
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t0: Vec (int);
    var $t1: int;
    var $t2: int;
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/random.move:41:5+1
    assume {:print "$at(3,1096,1097)"} true;
    assume $IsValid'vec'u8''($t0);

    // assume WellFormed($t1) at ./sources/random.move:41:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at ./sources/random.move:41:5+1
    assume $IsValid'u64'($t2);

    // trace_local[_seed]($t0) at ./sources/random.move:41:5+1
    assume {:print "$track_local(21,3,0):", $t0} $t0 == $t0;

    // trace_local[low]($t1) at ./sources/random.move:41:5+1
    assume {:print "$track_local(21,3,1):", $t1} $t1 == $t1;

    // trace_local[high]($t2) at ./sources/random.move:41:5+1
    assume {:print "$track_local(21,3,2):", $t2} $t2 == $t2;

    // $t3 := >($t2, $t1) at ./sources/random.move:42:22+1
    assume {:print "$at(3,1193,1194)"} true;
    call $t3 := $Gt($t2, $t1);

    // if ($t3) goto L1 else goto L0 at ./sources/random.move:42:9+54
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at ./sources/random.move:42:9+54
L1:

    // goto L2 at ./sources/random.move:42:9+54
    assume {:print "$at(3,1180,1234)"} true;
    goto L2;

    // label L0 at ./sources/random.move:42:29+33
L0:

    // $t4 := 101 at ./sources/random.move:42:29+33
    assume {:print "$at(3,1200,1233)"} true;
    $t4 := 101;
    assume $IsValid'u64'($t4);

    // trace_abort($t4) at ./sources/random.move:42:9+54
    assume {:print "$at(3,1180,1234)"} true;
    assume {:print "$track_abort(21,3):", $t4} $t4 == $t4;

    // $t5 := move($t4) at ./sources/random.move:42:9+54
    $t5 := $t4;

    // goto L4 at ./sources/random.move:42:9+54
    goto L4;

    // label L2 at ./sources/random.move:43:40+5
    assume {:print "$at(3,1275,1280)"} true;
L2:

    // $t6 := random::rand_u256_with_seed($t0) on_abort goto L4 with $t5 at ./sources/random.move:43:21+25
    assume {:print "$at(3,1256,1281)"} true;
    call $t6 := $0_random_rand_u256_with_seed($t0);
    if ($abort_flag) {
        assume {:print "$at(3,1256,1281)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(21,3):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t7 := -($t2, $t1) on_abort goto L4 with $t5 at ./sources/random.move:44:24+1
    assume {:print "$at(3,1306,1307)"} true;
    call $t7 := $Sub($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,1306,1307)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(21,3):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t8 := %($t6, $t7) on_abort goto L4 with $t5 at ./sources/random.move:44:16+1
    call $t8 := $Mod($t6, $t7);
    if ($abort_flag) {
        assume {:print "$at(3,1298,1299)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(21,3):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t9 := +($t8, $t1) on_abort goto L4 with $t5 at ./sources/random.move:44:32+1
    call $t9 := $Addu256($t8, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,1314,1315)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(21,3):", $t5} $t5 == $t5;
        goto L4;
    }

    // trace_return[0]($t9) at ./sources/random.move:44:9+28
    assume {:print "$track_return(21,3,0):", $t9} $t9 == $t9;

    // label L3 at ./sources/random.move:45:5+1
    assume {:print "$at(3,1324,1325)"} true;
L3:

    // return $t9 at ./sources/random.move:45:5+1
    assume {:print "$at(3,1324,1325)"} true;
    $ret0 := $t9;
    return;

    // label L4 at ./sources/random.move:45:5+1
L4:

    // abort($t5) at ./sources/random.move:45:5+1
    assume {:print "$at(3,1324,1325)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun random::rand_u256_with_seed [baseline] at ./sources/random.move:36:5+82
procedure {:inline 1} $0_random_rand_u256_with_seed(_$t0: Vec (int)) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: Vec (int);
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[_seed]($t0) at ./sources/random.move:36:5+1
    assume {:print "$at(3,952,953)"} true;
    assume {:print "$track_local(21,2,0):", $t0} $t0 == $t0;

    // $t1 := random::bytes_to_u256($t0) on_abort goto L2 with $t2 at ./sources/random.move:37:9+19
    assume {:print "$at(3,1009,1028)"} true;
    call $t1 := $0_random_bytes_to_u256($t0);
    if ($abort_flag) {
        assume {:print "$at(3,1009,1028)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(21,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at ./sources/random.move:37:9+19
    assume {:print "$track_return(21,2,0):", $t1} $t1 == $t1;

    // label L1 at ./sources/random.move:38:5+1
    assume {:print "$at(3,1033,1034)"} true;
L1:

    // return $t1 at ./sources/random.move:38:5+1
    assume {:print "$at(3,1033,1034)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/random.move:38:5+1
L2:

    // abort($t2) at ./sources/random.move:38:5+1
    assume {:print "$at(3,1033,1034)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun random::rand_u256_with_seed [verification] at ./sources/random.move:36:5+82
procedure {:timeLimit 40} $0_random_rand_u256_with_seed$verify(_$t0: Vec (int)) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: Vec (int);
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/random.move:36:5+1
    assume {:print "$at(3,952,953)"} true;
    assume $IsValid'vec'u8''($t0);

    // trace_local[_seed]($t0) at ./sources/random.move:36:5+1
    assume {:print "$track_local(21,2,0):", $t0} $t0 == $t0;

    // $t1 := random::bytes_to_u256($t0) on_abort goto L2 with $t2 at ./sources/random.move:37:9+19
    assume {:print "$at(3,1009,1028)"} true;
    call $t1 := $0_random_bytes_to_u256($t0);
    if ($abort_flag) {
        assume {:print "$at(3,1009,1028)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(21,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at ./sources/random.move:37:9+19
    assume {:print "$track_return(21,2,0):", $t1} $t1 == $t1;

    // label L1 at ./sources/random.move:38:5+1
    assume {:print "$at(3,1033,1034)"} true;
L1:

    // return $t1 at ./sources/random.move:38:5+1
    assume {:print "$at(3,1033,1034)"} true;
    $ret0 := $t1;
    return;

    // label L2 at ./sources/random.move:38:5+1
L2:

    // abort($t2) at ./sources/random.move:38:5+1
    assume {:print "$at(3,1033,1034)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun random::seed [baseline] at ./sources/random.move:11:5+442
procedure {:inline 1} $0_random_seed(_$t0: $Mutation ($2_tx_context_TxContext)) returns ($ret0: Vec (int), $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t1: Vec (int);
    var $t2: Vec (int);
    var $t3: $2_object_UID;
    var $t4: Vec (int);
    var $t5: $2_tx_context_TxContext;
    var $t6: Vec (int);
    var $t7: int;
    var $t8: $2_object_UID;
    var $t9: Vec (int);
    var $t10: $Mutation (Vec (int));
    var $t11: $Mutation (Vec (int));
    var $t12: Vec (int);
    var $t13: Vec (int);
    var $t0: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_object_UID': $2_object_UID;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[ctx]($t0) at ./sources/random.move:11:5+1
    assume {:print "$at(3,201,202)"} true;
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(21,0,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t5 := read_ref($t0) at ./sources/random.move:12:39+3
    assume {:print "$at(3,283,286)"} true;
    $t5 := $Dereference($t0);

    // $t6 := bcs::to_bytes<tx_context::TxContext>($t5) on_abort goto L2 with $t7 at ./sources/random.move:12:25+18
    call $t6 := $2_bcs_to_bytes'$2_tx_context_TxContext'($t5);
    if ($abort_flag) {
        assume {:print "$at(3,269,287)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[ctx_bytes#1#0]($t6) at ./sources/random.move:12:13+9
    assume {:print "$track_local(21,0,1):", $t6} $t6 == $t6;

    // $t8 := object::new($t0) on_abort goto L2 with $t7 at ./sources/random.move:13:19+16
    assume {:print "$at(3,307,323)"} true;
    call $t8,$t0 := $2_object_new($t0);
    if ($abort_flag) {
        assume {:print "$at(3,307,323)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[uid#1#0]($t8) at ./sources/random.move:13:13+3
    assume {:print "$track_local(21,0,3):", $t8} $t8 == $t8;

    // $t9 := object::uid_to_bytes($t8) on_abort goto L2 with $t7 at ./sources/random.move:14:37+26
    assume {:print "$at(3,361,387)"} true;
    call $t9 := $2_object_uid_to_bytes($t8);
    if ($abort_flag) {
        assume {:print "$at(3,361,387)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[uid_bytes#1#0]($t9) at ./sources/random.move:14:13+9
    assume {:print "$track_local(21,0,4):", $t9} $t9 == $t9;

    // object::delete($t8) on_abort goto L2 with $t7 at ./sources/random.move:15:9+19
    assume {:print "$at(3,397,416)"} true;
    call $2_object_delete($t8);
    if ($abort_flag) {
        assume {:print "$at(3,397,416)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t2 := vector::empty<u8>() on_abort goto L2 with $t7 at ./sources/random.move:17:32+19
    assume {:print "$at(3,450,469)"} true;
    call $t2 := $1_vector_empty'u8'();
    if ($abort_flag) {
        assume {:print "$at(3,450,469)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[info#1#0]($t2) at ./sources/random.move:17:13+4
    assume {:print "$track_local(21,0,2):", $t2} $t2 == $t2;

    // $t10 := borrow_local($t2) at ./sources/random.move:18:28+9
    assume {:print "$at(3,498,507)"} true;
    $t10 := $Mutation($Local(2), EmptyVec(), $t2);

    // vector::append<u8>($t10, $t6) on_abort goto L2 with $t7 at ./sources/random.move:18:9+40
    call $t10 := $1_vector_append'u8'($t10, $t6);
    if ($abort_flag) {
        assume {:print "$at(3,479,519)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // write_back[LocalRoot($t2)@]($t10) at ./sources/random.move:18:9+40
    $t2 := $Dereference($t10);

    // trace_local[info#1#0]($t2) at ./sources/random.move:18:9+40
    assume {:print "$track_local(21,0,2):", $t2} $t2 == $t2;

    // $t11 := borrow_local($t2) at ./sources/random.move:19:28+9
    assume {:print "$at(3,548,557)"} true;
    $t11 := $Mutation($Local(2), EmptyVec(), $t2);

    // vector::append<u8>($t11, $t9) on_abort goto L2 with $t7 at ./sources/random.move:19:9+40
    call $t11 := $1_vector_append'u8'($t11, $t9);
    if ($abort_flag) {
        assume {:print "$at(3,529,569)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // write_back[LocalRoot($t2)@]($t11) at ./sources/random.move:19:9+40
    $t2 := $Dereference($t11);

    // trace_local[info#1#0]($t2) at ./sources/random.move:19:9+40
    assume {:print "$track_local(21,0,2):", $t2} $t2 == $t2;

    // $t12 := move($t2) at ./sources/random.move:21:47+4
    assume {:print "$at(3,618,622)"} true;
    $t12 := $t2;

    // $t13 := hash::sha3_256($t12) on_abort goto L2 with $t7 at ./sources/random.move:21:32+20
    call $t13 := $1_hash_sha3_256($t12);
    if ($abort_flag) {
        assume {:print "$at(3,603,623)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_return[0]($t13) at ./sources/random.move:22:9+4
    assume {:print "$at(3,633,637)"} true;
    assume {:print "$track_return(21,0,0):", $t13} $t13 == $t13;

    // trace_local[ctx]($t0) at ./sources/random.move:22:9+4
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(21,0,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./sources/random.move:23:5+1
    assume {:print "$at(3,642,643)"} true;
L1:

    // return $t13 at ./sources/random.move:23:5+1
    assume {:print "$at(3,642,643)"} true;
    $ret0 := $t13;
    $ret1 := $t0;
    return;

    // label L2 at ./sources/random.move:23:5+1
L2:

    // abort($t7) at ./sources/random.move:23:5+1
    assume {:print "$at(3,642,643)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun random::seed [verification] at ./sources/random.move:11:5+442
procedure {:timeLimit 40} $0_random_seed$verify(_$t0: $Mutation ($2_tx_context_TxContext)) returns ($ret0: Vec (int), $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t1: Vec (int);
    var $t2: Vec (int);
    var $t3: $2_object_UID;
    var $t4: Vec (int);
    var $t5: $2_tx_context_TxContext;
    var $t6: Vec (int);
    var $t7: int;
    var $t8: $2_object_UID;
    var $t9: Vec (int);
    var $t10: $Mutation (Vec (int));
    var $t11: $Mutation (Vec (int));
    var $t12: Vec (int);
    var $t13: Vec (int);
    var $t0: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_object_UID': $2_object_UID;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/random.move:11:5+1
    assume {:print "$at(3,201,202)"} true;
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t0));

    // trace_local[ctx]($t0) at ./sources/random.move:11:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(21,0,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t5 := read_ref($t0) at ./sources/random.move:12:39+3
    assume {:print "$at(3,283,286)"} true;
    $t5 := $Dereference($t0);

    // $t6 := bcs::to_bytes<tx_context::TxContext>($t5) on_abort goto L2 with $t7 at ./sources/random.move:12:25+18
    call $t6 := $2_bcs_to_bytes'$2_tx_context_TxContext'($t5);
    if ($abort_flag) {
        assume {:print "$at(3,269,287)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[ctx_bytes#1#0]($t6) at ./sources/random.move:12:13+9
    assume {:print "$track_local(21,0,1):", $t6} $t6 == $t6;

    // $t8 := object::new($t0) on_abort goto L2 with $t7 at ./sources/random.move:13:19+16
    assume {:print "$at(3,307,323)"} true;
    call $t8,$t0 := $2_object_new($t0);
    if ($abort_flag) {
        assume {:print "$at(3,307,323)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[uid#1#0]($t8) at ./sources/random.move:13:13+3
    assume {:print "$track_local(21,0,3):", $t8} $t8 == $t8;

    // $t9 := object::uid_to_bytes($t8) on_abort goto L2 with $t7 at ./sources/random.move:14:37+26
    assume {:print "$at(3,361,387)"} true;
    call $t9 := $2_object_uid_to_bytes($t8);
    if ($abort_flag) {
        assume {:print "$at(3,361,387)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[uid_bytes#1#0]($t9) at ./sources/random.move:14:13+9
    assume {:print "$track_local(21,0,4):", $t9} $t9 == $t9;

    // object::delete($t8) on_abort goto L2 with $t7 at ./sources/random.move:15:9+19
    assume {:print "$at(3,397,416)"} true;
    call $2_object_delete($t8);
    if ($abort_flag) {
        assume {:print "$at(3,397,416)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t2 := vector::empty<u8>() on_abort goto L2 with $t7 at ./sources/random.move:17:32+19
    assume {:print "$at(3,450,469)"} true;
    call $t2 := $1_vector_empty'u8'();
    if ($abort_flag) {
        assume {:print "$at(3,450,469)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[info#1#0]($t2) at ./sources/random.move:17:13+4
    assume {:print "$track_local(21,0,2):", $t2} $t2 == $t2;

    // $t10 := borrow_local($t2) at ./sources/random.move:18:28+9
    assume {:print "$at(3,498,507)"} true;
    $t10 := $Mutation($Local(2), EmptyVec(), $t2);

    // vector::append<u8>($t10, $t6) on_abort goto L2 with $t7 at ./sources/random.move:18:9+40
    call $t10 := $1_vector_append'u8'($t10, $t6);
    if ($abort_flag) {
        assume {:print "$at(3,479,519)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // write_back[LocalRoot($t2)@]($t10) at ./sources/random.move:18:9+40
    $t2 := $Dereference($t10);

    // trace_local[info#1#0]($t2) at ./sources/random.move:18:9+40
    assume {:print "$track_local(21,0,2):", $t2} $t2 == $t2;

    // $t11 := borrow_local($t2) at ./sources/random.move:19:28+9
    assume {:print "$at(3,548,557)"} true;
    $t11 := $Mutation($Local(2), EmptyVec(), $t2);

    // vector::append<u8>($t11, $t9) on_abort goto L2 with $t7 at ./sources/random.move:19:9+40
    call $t11 := $1_vector_append'u8'($t11, $t9);
    if ($abort_flag) {
        assume {:print "$at(3,529,569)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // write_back[LocalRoot($t2)@]($t11) at ./sources/random.move:19:9+40
    $t2 := $Dereference($t11);

    // trace_local[info#1#0]($t2) at ./sources/random.move:19:9+40
    assume {:print "$track_local(21,0,2):", $t2} $t2 == $t2;

    // $t12 := move($t2) at ./sources/random.move:21:47+4
    assume {:print "$at(3,618,622)"} true;
    $t12 := $t2;

    // $t13 := hash::sha3_256($t12) on_abort goto L2 with $t7 at ./sources/random.move:21:32+20
    call $t13 := $1_hash_sha3_256($t12);
    if ($abort_flag) {
        assume {:print "$at(3,603,623)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(21,0):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_return[0]($t13) at ./sources/random.move:22:9+4
    assume {:print "$at(3,633,637)"} true;
    assume {:print "$track_return(21,0,0):", $t13} $t13 == $t13;

    // trace_local[ctx]($t0) at ./sources/random.move:22:9+4
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(21,0,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./sources/random.move:23:5+1
    assume {:print "$at(3,642,643)"} true;
L1:

    // return $t13 at ./sources/random.move:23:5+1
    assume {:print "$at(3,642,643)"} true;
    $ret0 := $t13;
    $ret1 := $t0;
    return;

    // label L2 at ./sources/random.move:23:5+1
L2:

    // abort($t7) at ./sources/random.move:23:5+1
    assume {:print "$at(3,642,643)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun coinFilp::play [verification] at ./sources/coinFilp.move:23:5+794
procedure {:timeLimit 40} $0_coinFilp_play$verify(_$t0: $Mutation ($0_vault_Vault'#0_#1'), _$t1: $2_coin_Coin'#0', _$t2: int, _$t3: int, _$t4: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $Mutation ($0_vault_Vault'#0_#1'), $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t5: bool;
    var $t6: bool;
    var $t7: bool;
    var $t8: bool;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: $2_tx_context_TxContext;
    var $t14: int;
    var $t15: int;
    var $t16: $2_coin_Coin'#0';
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t20: int;
    var $t21: int;
    var $t22: int;
    var $t23: bool;
    var $t24: int;
    var $t25: int;
    var $t26: bool;
    var $t27: bool;
    var $t28: int;
    var $t29: int;
    var $t30: $Mutation ($2_coin_Coin'#0');
    var $t31: int;
    var $t32: $2_coin_Coin'#0';
    var $t33: int;
    var $t34: int;
    var $t35: int;
    var $t36: int;
    var $t37: bool;
    var $t38: int;
    var $t39: bool;
    var $t40: bool;
    var $t41: int;
    var $t42: bool;
    var $t43: int;
    var $t44: bool;
    var $t45: $2_coin_Coin'#0';
    var $t46: $2_coin_Coin'#0';
    var $t47: $2_coin_Coin'#0';
    var $t0: $Mutation ($0_vault_Vault'#0_#1');
    var $t1: $2_coin_Coin'#0';
    var $t2: int;
    var $t3: int;
    var $t4: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$0_vault_Vault'#0_#1'': $0_vault_Vault'#0_#1';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;
    $t4 := _$t4;

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);
    assume l#$Mutation($t4) == $Param(4);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/coinFilp.move:23:5+1
    assume {:print "$at(2,536,537)"} true;
    assume $IsValid'$0_vault_Vault'#0_#1''($Dereference($t0));

    // assume WellFormed($t1) at ./sources/coinFilp.move:23:5+1
    assume $IsValid'$2_coin_Coin'#0''($t1);

    // assume WellFormed($t2) at ./sources/coinFilp.move:23:5+1
    assume $IsValid'u64'($t2);

    // assume WellFormed($t3) at ./sources/coinFilp.move:23:5+1
    assume $IsValid'u64'($t3);

    // assume WellFormed($t4) at ./sources/coinFilp.move:23:5+1
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t4));

    // trace_local[v]($t0) at ./sources/coinFilp.move:23:5+1
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(22,0,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[paid]($t1) at ./sources/coinFilp.move:23:5+1
    assume {:print "$track_local(22,0,1):", $t1} $t1 == $t1;

    // trace_local[amount]($t2) at ./sources/coinFilp.move:23:5+1
    assume {:print "$track_local(22,0,2):", $t2} $t2 == $t2;

    // trace_local[number]($t3) at ./sources/coinFilp.move:23:5+1
    assume {:print "$track_local(22,0,3):", $t3} $t3 == $t3;

    // trace_local[ctx]($t4) at ./sources/coinFilp.move:23:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t4);
    assume {:print "$track_local(22,0,4):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t13 := read_ref($t4) at ./sources/coinFilp.move:24:41+3
    assume {:print "$at(2,686,689)"} true;
    $t13 := $Dereference($t4);

    // $t14 := tx_context::sender($t13) on_abort goto L22 with $t15 at ./sources/coinFilp.move:24:22+23
    call $t14 := $2_tx_context_sender($t13);
    if ($abort_flag) {
        assume {:print "$at(2,667,690)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(22,0):", $t15} $t15 == $t15;
        goto L22;
    }

    // trace_local[sender#1#0]($t14) at ./sources/coinFilp.move:24:13+6
    assume {:print "$track_local(22,0,11):", $t14} $t14 == $t14;

    // $t16 := copy($t1) at ./sources/coinFilp.move:25:33+5
    assume {:print "$at(2,724,729)"} true;
    $t16 := $t1;

    // $t17 := coin::value<#0>($t16) on_abort goto L22 with $t15 at ./sources/coinFilp.move:25:21+18
    call $t17 := $2_coin_value'#0'($t16);
    if ($abort_flag) {
        assume {:print "$at(2,712,730)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(22,0):", $t15} $t15 == $t15;
        goto L22;
    }

    // trace_local[value#1#0]($t17) at ./sources/coinFilp.move:25:13+5
    assume {:print "$track_local(22,0,12):", $t17} $t17 == $t17;

    // $t18 := 2 at ./sources/coinFilp.move:26:32+1
    assume {:print "$at(2,763,764)"} true;
    $t18 := 2;
    assume $IsValid'u64'($t18);

    // $t19 := *($t2, $t18) on_abort goto L22 with $t15 at ./sources/coinFilp.move:26:30+1
    call $t19 := $Mulu256($t2, $t18);
    if ($abort_flag) {
        assume {:print "$at(2,761,762)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(22,0):", $t15} $t15 == $t15;
        goto L22;
    }

    // $t20 := 100 at ./sources/coinFilp.move:26:36+3
    $t20 := 100;
    assume $IsValid'u64'($t20);

    // $t21 := /($t19, $t20) on_abort goto L22 with $t15 at ./sources/coinFilp.move:26:34+1
    call $t21 := $Div($t19, $t20);
    if ($abort_flag) {
        assume {:print "$at(2,765,766)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(22,0):", $t15} $t15 == $t15;
        goto L22;
    }

    // trace_local[funding#1#0]($t21) at ./sources/coinFilp.move:26:13+7
    assume {:print "$track_local(22,0,9):", $t21} $t21 == $t21;

    // $t22 := +($t2, $t21) on_abort goto L22 with $t15 at ./sources/coinFilp.move:27:32+1
    assume {:print "$at(2,803,804)"} true;
    call $t22 := $Addu256($t2, $t21);
    if ($abort_flag) {
        assume {:print "$at(2,803,804)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(22,0):", $t15} $t15 == $t15;
        goto L22;
    }

    // $t23 := ==($t17, $t22) at ./sources/coinFilp.move:27:23+2
    $t23 := $IsEqual'u64'($t17, $t22);

    // if ($t23) goto L1 else goto L0 at ./sources/coinFilp.move:27:9+36
    if ($t23) { goto L1; } else { goto L0; }

    // label L1 at ./sources/coinFilp.move:27:9+36
L1:

    // goto L2 at ./sources/coinFilp.move:27:9+36
    assume {:print "$at(2,780,816)"} true;
    goto L2;

    // label L0 at ./sources/coinFilp.move:27:9+36
L0:

    // destroy($t0) at ./sources/coinFilp.move:27:9+36
    assume {:print "$at(2,780,816)"} true;

    // destroy($t4) at ./sources/coinFilp.move:27:9+36

    // $t24 := 99 at ./sources/coinFilp.move:27:42+2
    $t24 := 99;
    assume $IsValid'u64'($t24);

    // trace_abort($t24) at ./sources/coinFilp.move:27:9+36
    assume {:print "$at(2,780,816)"} true;
    assume {:print "$track_abort(22,0):", $t24} $t24 == $t24;

    // $t15 := move($t24) at ./sources/coinFilp.move:27:9+36
    $t15 := $t24;

    // goto L22 at ./sources/coinFilp.move:27:9+36
    goto L22;

    // label L2 at ./sources/coinFilp.move:28:17+6
    assume {:print "$at(2,834,840)"} true;
L2:

    // $t25 := 0 at ./sources/coinFilp.move:28:27+1
    assume {:print "$at(2,844,845)"} true;
    $t25 := 0;
    assume $IsValid'u64'($t25);

    // $t26 := ==($t3, $t25) at ./sources/coinFilp.move:28:24+2
    $t26 := $IsEqual'u64'($t3, $t25);

    // if ($t26) goto L4 else goto L3 at ./sources/coinFilp.move:28:17+26
    if ($t26) { goto L4; } else { goto L3; }

    // label L4 at ./sources/coinFilp.move:28:17+26
L4:

    // $t27 := true at ./sources/coinFilp.move:28:17+26
    assume {:print "$at(2,834,860)"} true;
    $t27 := true;
    assume $IsValid'bool'($t27);

    // $t5 := $t27 at ./sources/coinFilp.move:28:17+26
    $t5 := $t27;

    // goto L5 at ./sources/coinFilp.move:28:17+26
    goto L5;

    // label L3 at ./sources/coinFilp.move:28:32+6
L3:

    // $t28 := 1 at ./sources/coinFilp.move:28:42+1
    assume {:print "$at(2,859,860)"} true;
    $t28 := 1;
    assume $IsValid'u64'($t28);

    // $t5 := ==($t3, $t28) at ./sources/coinFilp.move:28:39+2
    $t5 := $IsEqual'u64'($t3, $t28);

    // label L5 at ./sources/coinFilp.move:28:17+26
L5:

    // if ($t5) goto L7 else goto L6 at ./sources/coinFilp.move:28:9+37
    assume {:print "$at(2,826,863)"} true;
    if ($t5) { goto L7; } else { goto L6; }

    // label L7 at ./sources/coinFilp.move:28:9+37
L7:

    // goto L8 at ./sources/coinFilp.move:28:9+37
    assume {:print "$at(2,826,863)"} true;
    goto L8;

    // label L6 at ./sources/coinFilp.move:28:9+37
L6:

    // destroy($t0) at ./sources/coinFilp.move:28:9+37
    assume {:print "$at(2,826,863)"} true;

    // destroy($t4) at ./sources/coinFilp.move:28:9+37

    // $t29 := 1 at ./sources/coinFilp.move:28:44+1
    $t29 := 1;
    assume $IsValid'u64'($t29);

    // trace_abort($t29) at ./sources/coinFilp.move:28:9+37
    assume {:print "$at(2,826,863)"} true;
    assume {:print "$track_abort(22,0):", $t29} $t29 == $t29;

    // $t15 := move($t29) at ./sources/coinFilp.move:28:9+37
    $t15 := $t29;

    // goto L22 at ./sources/coinFilp.move:28:9+37
    goto L22;

    // label L8 at ./sources/coinFilp.move:30:37+9
    assume {:print "$at(2,902,911)"} true;
L8:

    // $t30 := borrow_local($t1) at ./sources/coinFilp.move:30:37+9
    assume {:print "$at(2,902,911)"} true;
    $t30 := $Mutation($Local(1), EmptyVec(), $t1);

    // assume Identical($t31, select balance::Balance.value(select coin::Coin.balance($t30))) at /home/yusong/.move/https___github_com_MystenLabs_sui_git_testnet/crates/sui-framework/packages/sui-framework/sources/coin.move:187:9+36
    assume {:print "$at(29,6343,6379)"} true;
    assume ($t31 == $value#$2_balance_Balance'#0'($balance#$2_coin_Coin'#0'($Dereference($t30))));

    // $t32 := coin::split<#0>($t30, $t21, $t4) on_abort goto L22 with $t15 at ./sources/coinFilp.move:30:25+35
    assume {:print "$at(2,890,925)"} true;
    call $t32,$t30,$t4 := $2_coin_split'#0'($t30, $t21, $t4);
    if ($abort_flag) {
        assume {:print "$at(2,890,925)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(22,0):", $t15} $t15 == $t15;
        goto L22;
    }

    // write_back[LocalRoot($t1)@]($t30) at ./sources/coinFilp.move:30:25+35
    $t1 := $Dereference($t30);

    // trace_local[paid]($t1) at ./sources/coinFilp.move:30:25+35
    assume {:print "$track_local(22,0,1):", $t1} $t1 == $t1;

    // transfer::public_transfer<coin::Coin<#0>>($t32, $t14) on_abort goto L22 with $t15 at ./sources/coinFilp.move:31:9+35
    assume {:print "$at(2,935,970)"} true;
    call $2_transfer_public_transfer'$2_coin_Coin'#0''($t32, $t14);
    if ($abort_flag) {
        assume {:print "$at(2,935,970)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(22,0):", $t15} $t15 == $t15;
        goto L22;
    }

    // $t33 := 0 at ./sources/coinFilp.move:32:52+1
    assume {:print "$at(2,1023,1024)"} true;
    $t33 := 0;
    assume $IsValid'u64'($t33);

    // $t34 := 99 at ./sources/coinFilp.move:32:54+2
    $t34 := 99;
    assume $IsValid'u64'($t34);

    // $t35 := random::rand_u256_range($t33, $t34, $t4) on_abort goto L22 with $t15 at ./sources/coinFilp.move:32:29+32
    call $t35,$t4 := $0_random_rand_u256_range($t33, $t34, $t4);
    if ($abort_flag) {
        assume {:print "$at(2,1000,1032)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(22,0):", $t15} $t15 == $t15;
        goto L22;
    }

    // trace_local[random_number#1#0]($t35) at ./sources/coinFilp.move:32:13+13
    assume {:print "$track_local(22,0,10):", $t35} $t35 == $t35;

    // $t36 := 0 at ./sources/coinFilp.move:33:24+1
    assume {:print "$at(2,1057,1058)"} true;
    $t36 := 0;
    assume $IsValid'u64'($t36);

    // $t37 := ==($t3, $t36) at ./sources/coinFilp.move:33:21+2
    $t37 := $IsEqual'u64'($t3, $t36);

    // if ($t37) goto L10 else goto L9 at ./sources/coinFilp.move:33:13+35
    if ($t37) { goto L10; } else { goto L9; }

    // label L10 at ./sources/coinFilp.move:33:29+13
L10:

    // $t38 := 49 at ./sources/coinFilp.move:33:45+2
    assume {:print "$at(2,1078,1080)"} true;
    $t38 := 49;
    assume $IsValid'u64'($t38);

    // $t6 := <($t35, $t38) at ./sources/coinFilp.move:33:43+1
    call $t6 := $Lt($t35, $t38);

    // goto L11 at ./sources/coinFilp.move:33:13+35
    goto L11;

    // label L9 at ./sources/coinFilp.move:33:13+35
L9:

    // $t39 := false at ./sources/coinFilp.move:33:13+35
    assume {:print "$at(2,1046,1081)"} true;
    $t39 := false;
    assume $IsValid'bool'($t39);

    // $t6 := $t39 at ./sources/coinFilp.move:33:13+35
    $t6 := $t39;

    // label L11 at ./sources/coinFilp.move:33:13+35
L11:

    // if ($t6) goto L13 else goto L12 at ./sources/coinFilp.move:33:13+74
    assume {:print "$at(2,1046,1120)"} true;
    if ($t6) { goto L13; } else { goto L12; }

    // label L13 at ./sources/coinFilp.move:33:13+74
L13:

    // $t40 := true at ./sources/coinFilp.move:33:13+74
    assume {:print "$at(2,1046,1120)"} true;
    $t40 := true;
    assume $IsValid'bool'($t40);

    // $t8 := $t40 at ./sources/coinFilp.move:33:13+74
    $t8 := $t40;

    // goto L14 at ./sources/coinFilp.move:33:13+74
    goto L14;

    // label L12 at ./sources/coinFilp.move:33:53+6
L12:

    // $t41 := 1 at ./sources/coinFilp.move:33:63+1
    assume {:print "$at(2,1096,1097)"} true;
    $t41 := 1;
    assume $IsValid'u64'($t41);

    // $t42 := ==($t3, $t41) at ./sources/coinFilp.move:33:60+2
    $t42 := $IsEqual'u64'($t3, $t41);

    // if ($t42) goto L16 else goto L15 at ./sources/coinFilp.move:33:52+35
    if ($t42) { goto L16; } else { goto L15; }

    // label L16 at ./sources/coinFilp.move:33:68+13
L16:

    // $t43 := 50 at ./sources/coinFilp.move:33:84+2
    assume {:print "$at(2,1117,1119)"} true;
    $t43 := 50;
    assume $IsValid'u64'($t43);

    // $t7 := >($t35, $t43) at ./sources/coinFilp.move:33:82+1
    call $t7 := $Gt($t35, $t43);

    // goto L17 at ./sources/coinFilp.move:33:52+35
    goto L17;

    // label L15 at ./sources/coinFilp.move:33:52+35
L15:

    // $t44 := false at ./sources/coinFilp.move:33:52+35
    assume {:print "$at(2,1085,1120)"} true;
    $t44 := false;
    assume $IsValid'bool'($t44);

    // $t7 := $t44 at ./sources/coinFilp.move:33:52+35
    $t7 := $t44;

    // label L17 at ./sources/coinFilp.move:33:52+35
L17:

    // $t8 := $t7 at ./sources/coinFilp.move:33:13+74
    assume {:print "$at(2,1046,1120)"} true;
    $t8 := $t7;

    // label L14 at ./sources/coinFilp.move:33:13+74
L14:

    // if ($t8) goto L19 else goto L18 at ./sources/coinFilp.move:33:9+282
    assume {:print "$at(2,1042,1324)"} true;
    if ($t8) { goto L19; } else { goto L18; }

    // label L19 at ./sources/coinFilp.move:35:42+1
    assume {:print "$at(2,1182,1183)"} true;
L19:

    // $t45 := move($t1) at ./sources/coinFilp.move:35:45+4
    assume {:print "$at(2,1185,1189)"} true;
    $t45 := $t1;

    // $t46 := vault::lose<#0, #1>($t0, $t45, $t4) on_abort goto L22 with $t15 at ./sources/coinFilp.move:35:23+32
    call $t46,$t0,$t4 := $0_vault_lose'#0_#1'($t0, $t45, $t4);
    if ($abort_flag) {
        assume {:print "$at(2,1163,1195)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(22,0):", $t15} $t15 == $t15;
        goto L22;
    }

    // transfer::public_transfer<coin::Coin<#0>>($t46, $t14) on_abort goto L22 with $t15 at ./sources/coinFilp.move:36:13+28
    assume {:print "$at(2,1209,1237)"} true;
    call $2_transfer_public_transfer'$2_coin_Coin'#0''($t46, $t14);
    if ($abort_flag) {
        assume {:print "$at(2,1209,1237)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(22,0):", $t15} $t15 == $t15;
        goto L22;
    }

    // goto L20 at ./sources/coinFilp.move:33:9+282
    assume {:print "$at(2,1042,1324)"} true;
    goto L20;

    // label L18 at ./sources/coinFilp.move:39:13+26
    assume {:print "$at(2,1287,1313)"} true;
L18:

    // destroy($t4) at ./sources/coinFilp.move:39:13+26
    assume {:print "$at(2,1287,1313)"} true;

    // $t47 := move($t1) at ./sources/coinFilp.move:39:34+4
    $t47 := $t1;

    // vault::win<#0, #1>($t0, $t47) on_abort goto L22 with $t15 at ./sources/coinFilp.move:39:13+26
    call $t0 := $0_vault_win'#0_#1'($t0, $t47);
    if ($abort_flag) {
        assume {:print "$at(2,1287,1313)"} true;
        $t15 := $abort_code;
        assume {:print "$track_abort(22,0):", $t15} $t15 == $t15;
        goto L22;
    }

    // label L20 at ./sources/coinFilp.move:33:9+282
    assume {:print "$at(2,1042,1324)"} true;
L20:

    // trace_local[v]($t0) at ./sources/coinFilp.move:33:9+282
    assume {:print "$at(2,1042,1324)"} true;
    $temp_0'$0_vault_Vault'#0_#1'' := $Dereference($t0);
    assume {:print "$track_local(22,0,0):", $temp_0'$0_vault_Vault'#0_#1''} $temp_0'$0_vault_Vault'#0_#1'' == $temp_0'$0_vault_Vault'#0_#1'';

    // trace_local[ctx]($t4) at ./sources/coinFilp.move:33:9+282
    $temp_0'$2_tx_context_TxContext' := $Dereference($t4);
    assume {:print "$track_local(22,0,4):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L21 at ./sources/coinFilp.move:41:5+1
    assume {:print "$at(2,1329,1330)"} true;
L21:

    // return () at ./sources/coinFilp.move:41:5+1
    assume {:print "$at(2,1329,1330)"} true;
    $ret0 := $t0;
    $ret1 := $t4;
    return;

    // label L22 at ./sources/coinFilp.move:41:5+1
L22:

    // abort($t15) at ./sources/coinFilp.move:41:5+1
    assume {:print "$at(2,1329,1330)"} true;
    $abort_code := $t15;
    $abort_flag := true;
    return;

}
