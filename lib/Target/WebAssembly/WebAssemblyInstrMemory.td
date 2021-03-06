// WebAssemblyInstrMemory.td-WebAssembly Memory codegen support -*- tablegen -*-
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// WebAssembly Memory operand code-gen constructs.
///
//===----------------------------------------------------------------------===//

// TODO:
//  - HasAddr64
//  - WebAssemblyTargetLowering having to do with atomics
//  - Each has optional alignment.

// WebAssembly has i8/i16/i32/i64/f32/f64 memory types, but doesn't have i8/i16
// local types. These memory-only types instead zero- or sign-extend into local
// types when loading, and truncate when storing.

// WebAssembly constant offsets are performed as unsigned with infinite
// precision, so we need to check for NoUnsignedWrap so that we don't fold an
// offset for an add that needs wrapping.
def regPlusImm : PatFrag<(ops node:$addr, node:$off),
                         (add node:$addr, node:$off),
                         [{ return N->getFlags().hasNoUnsignedWrap(); }]>;

// Treat an 'or' node as an 'add' if the or'ed bits are known to be zero.
def or_is_add : PatFrag<(ops node:$lhs, node:$rhs), (or node:$lhs, node:$rhs),[{
  if (ConstantSDNode *CN = dyn_cast<ConstantSDNode>(N->getOperand(1)))
    return CurDAG->MaskedValueIsZero(N->getOperand(0), CN->getAPIntValue());

  KnownBits Known0;
  CurDAG->computeKnownBits(N->getOperand(0), Known0, 0);
  KnownBits Known1;
  CurDAG->computeKnownBits(N->getOperand(1), Known1, 0);
  return (~Known0.Zero & ~Known1.Zero) == 0;
}]>;

// GlobalAddresses are conceptually unsigned values, so we can also fold them
// into immediate values as long as the add is 'nuw'.
// TODO: We'd like to also match GA offsets but there are cases where the
// register can have a negative value. Find out what more we can do.
def regPlusGA : PatFrag<(ops node:$addr, node:$off),
                        (add node:$addr, node:$off),
                        [{
  return N->getFlags().hasNoUnsignedWrap();
}]>;

// We don't need a regPlusES because external symbols never have constant
// offsets folded into them, so we can just use add.

let Defs = [ARGUMENTS] in {

// Defines atomic and non-atomic loads, regular and extending.
class WebAssemblyLoad<WebAssemblyRegClass rc, string Name, int Opcode> :
  I<(outs rc:$dst),
    (ins P2Align:$p2align, offset32_op:$off, I32:$addr),
    [], !strconcat(Name, "\t$dst, ${off}(${addr})${p2align}"), Opcode>;

// Basic load.
// FIXME: When we can break syntax compatibility, reorder the fields in the
// asmstrings to match the binary encoding.
def LOAD_I32 : WebAssemblyLoad<I32, "i32.load", 0x28>;
def LOAD_I64 : WebAssemblyLoad<I64, "i64.load", 0x29>;
def LOAD_F32 : WebAssemblyLoad<F32, "f32.load", 0x2a>;
def LOAD_F64 : WebAssemblyLoad<F64, "f64.load", 0x2b>;

} // Defs = [ARGUMENTS]

// Select loads with no constant offset.
class LoadPatNoOffset<ValueType ty, PatFrag node, I inst> :
  Pat<(ty (node I32:$addr)), (inst 0, 0, $addr)>;

def : LoadPatNoOffset<i32, load, LOAD_I32>;
def : LoadPatNoOffset<i64, load, LOAD_I64>;
def : LoadPatNoOffset<f32, load, LOAD_F32>;
def : LoadPatNoOffset<f64, load, LOAD_F64>;


// Select loads with a constant offset.

// Pattern with address + immediate offset
class LoadPatImmOff<ValueType ty, PatFrag loadkind, PatFrag operand, I inst> :
  Pat<(ty (loadkind (operand I32:$addr, imm:$off))),
      (inst 0, imm:$off, $addr)>;

def : LoadPatImmOff<i32, load, regPlusImm, LOAD_I32>;
def : LoadPatImmOff<i64, load, regPlusImm, LOAD_I64>;
def : LoadPatImmOff<f32, load, regPlusImm, LOAD_F32>;
def : LoadPatImmOff<f64, load, regPlusImm, LOAD_F64>;
def : LoadPatImmOff<i32, load, or_is_add, LOAD_I32>;
def : LoadPatImmOff<i64, load, or_is_add, LOAD_I64>;
def : LoadPatImmOff<f32, load, or_is_add, LOAD_F32>;
def : LoadPatImmOff<f64, load, or_is_add, LOAD_F64>;

class LoadPatGlobalAddr<ValueType ty, PatFrag loadkind, I inst> :
  Pat<(ty (loadkind (regPlusGA I32:$addr, (WebAssemblywrapper tglobaladdr:$off)))),
      (inst 0, tglobaladdr:$off, $addr)>;

def : LoadPatGlobalAddr<i32, load, LOAD_I32>;
def : LoadPatGlobalAddr<i64, load, LOAD_I64>;
def : LoadPatGlobalAddr<f32, load, LOAD_F32>;
def : LoadPatGlobalAddr<f64, load, LOAD_F64>;

class LoadPatExternalSym<ValueType ty, PatFrag loadkind, I inst> :
  Pat<(ty (loadkind (add I32:$addr, (WebAssemblywrapper texternalsym:$off)))),
      (inst 0, texternalsym:$off, $addr)>;
def : LoadPatExternalSym<i32, load, LOAD_I32>;
def : LoadPatExternalSym<i64, load, LOAD_I64>;
def : LoadPatExternalSym<f32, load, LOAD_F32>;
def : LoadPatExternalSym<f64, load, LOAD_F64>;


// Select loads with just a constant offset.
class LoadPatOffsetOnly<ValueType ty, PatFrag loadkind, I inst> :
  Pat<(ty (loadkind imm:$off)), (inst 0, imm:$off, (CONST_I32 0))>;

def : LoadPatOffsetOnly<i32, load, LOAD_I32>;
def : LoadPatOffsetOnly<i64, load, LOAD_I64>;
def : LoadPatOffsetOnly<f32, load, LOAD_F32>;
def : LoadPatOffsetOnly<f64, load, LOAD_F64>;

class LoadPatGlobalAddrOffOnly<ValueType ty, PatFrag loadkind, I inst> :
  Pat<(ty (loadkind (WebAssemblywrapper tglobaladdr:$off))),
      (inst 0, tglobaladdr:$off, (CONST_I32 0))>;

def : LoadPatGlobalAddrOffOnly<i32, load, LOAD_I32>;
def : LoadPatGlobalAddrOffOnly<i64, load, LOAD_I64>;
def : LoadPatGlobalAddrOffOnly<f32, load, LOAD_F32>;
def : LoadPatGlobalAddrOffOnly<f64, load, LOAD_F64>;

class LoadPatExternSymOffOnly<ValueType ty, PatFrag loadkind, I inst> :
  Pat<(ty (loadkind (WebAssemblywrapper texternalsym:$off))),
      (inst 0, texternalsym:$off, (CONST_I32 0))>;
def : LoadPatExternSymOffOnly<i32, load, LOAD_I32>;
def : LoadPatExternSymOffOnly<i64, load, LOAD_I64>;
def : LoadPatExternSymOffOnly<f32, load, LOAD_F32>;
def : LoadPatExternSymOffOnly<f64, load, LOAD_F64>;

let Defs = [ARGUMENTS] in {

// Extending load.
def LOAD8_S_I32 : WebAssemblyLoad<I32, "i32.load8_s", 0x2c>;
def LOAD8_U_I32 : WebAssemblyLoad<I32, "i32.load8_u", 0x2d>;
def LOAD16_S_I32 : WebAssemblyLoad<I32, "i32.load16_s", 0x2e>;
def LOAD16_U_I32 : WebAssemblyLoad<I32, "i32.load16_u", 0x2f>;
def LOAD8_S_I64 : WebAssemblyLoad<I64, "i64.load8_s", 0x30>;
def LOAD8_U_I64 : WebAssemblyLoad<I64, "i64.load8_u", 0x31>;
def LOAD16_S_I64 : WebAssemblyLoad<I64, "i64.load16_s", 0x32>;
def LOAD16_U_I64 : WebAssemblyLoad<I64, "i64.load16_u", 0x33>;
def LOAD32_S_I64 : WebAssemblyLoad<I64, "i64.load32_s", 0x34>;
def LOAD32_U_I64 : WebAssemblyLoad<I64, "i64.load32_u", 0x35>;

} // Defs = [ARGUMENTS]

// Select extending loads with no constant offset.
def : LoadPatNoOffset<i32, sextloadi8, LOAD8_S_I32>;
def : LoadPatNoOffset<i32, zextloadi8, LOAD8_U_I32>;
def : LoadPatNoOffset<i32, sextloadi16, LOAD16_S_I32>;
def : LoadPatNoOffset<i32, zextloadi16, LOAD16_U_I32>;
def : LoadPatNoOffset<i64, sextloadi8, LOAD8_S_I64>;
def : LoadPatNoOffset<i64, zextloadi8, LOAD8_U_I64>;
def : LoadPatNoOffset<i64, sextloadi16, LOAD16_S_I64>;
def : LoadPatNoOffset<i64, zextloadi16, LOAD16_U_I64>;
def : LoadPatNoOffset<i64, sextloadi32, LOAD32_S_I64>;
def : LoadPatNoOffset<i64, zextloadi32, LOAD32_U_I64>;

// Select extending loads with a constant offset.
def : LoadPatImmOff<i32, sextloadi8, regPlusImm, LOAD8_S_I32>;
def : LoadPatImmOff<i32, zextloadi8, regPlusImm, LOAD8_U_I32>;
def : LoadPatImmOff<i32, sextloadi16, regPlusImm, LOAD16_S_I32>;
def : LoadPatImmOff<i32, zextloadi16, regPlusImm, LOAD16_U_I32>;
def : LoadPatImmOff<i64, sextloadi8, regPlusImm, LOAD8_S_I64>;
def : LoadPatImmOff<i64, zextloadi8, regPlusImm, LOAD8_U_I64>;
def : LoadPatImmOff<i64, sextloadi16, regPlusImm, LOAD16_S_I64>;
def : LoadPatImmOff<i64, zextloadi16, regPlusImm, LOAD16_U_I64>;
def : LoadPatImmOff<i64, sextloadi32, regPlusImm, LOAD32_S_I64>;
def : LoadPatImmOff<i64, zextloadi32, regPlusImm, LOAD32_U_I64>;

def : LoadPatImmOff<i32, sextloadi8, or_is_add, LOAD8_S_I32>;
def : LoadPatImmOff<i32, zextloadi8, or_is_add, LOAD8_U_I32>;
def : LoadPatImmOff<i32, sextloadi16, or_is_add, LOAD16_S_I32>;
def : LoadPatImmOff<i32, zextloadi16, or_is_add, LOAD16_U_I32>;
def : LoadPatImmOff<i64, sextloadi8, or_is_add, LOAD8_S_I64>;
def : LoadPatImmOff<i64, zextloadi8, or_is_add, LOAD8_U_I64>;
def : LoadPatImmOff<i64, sextloadi16, or_is_add, LOAD16_S_I64>;
def : LoadPatImmOff<i64, zextloadi16, or_is_add, LOAD16_U_I64>;
def : LoadPatImmOff<i64, sextloadi32, or_is_add, LOAD32_S_I64>;
def : LoadPatImmOff<i64, zextloadi32, or_is_add, LOAD32_U_I64>;

def : LoadPatGlobalAddr<i32, sextloadi8, LOAD8_S_I32>;
def : LoadPatGlobalAddr<i32, zextloadi8, LOAD8_U_I32>;
def : LoadPatGlobalAddr<i32, sextloadi16, LOAD16_S_I32>;
def : LoadPatGlobalAddr<i32, zextloadi8, LOAD16_U_I32>;

def : LoadPatGlobalAddr<i64, sextloadi8, LOAD8_S_I64>;
def : LoadPatGlobalAddr<i64, zextloadi8, LOAD8_U_I64>;
def : LoadPatGlobalAddr<i64, sextloadi16, LOAD16_S_I64>;
def : LoadPatGlobalAddr<i64, zextloadi16, LOAD16_U_I64>;
def : LoadPatGlobalAddr<i64, sextloadi32, LOAD32_S_I64>;
def : LoadPatGlobalAddr<i64, zextloadi32, LOAD32_U_I64>;

def : LoadPatExternalSym<i32, sextloadi8, LOAD8_S_I32>;
def : LoadPatExternalSym<i32, zextloadi8, LOAD8_U_I32>;
def : LoadPatExternalSym<i32, sextloadi16, LOAD16_S_I32>;
def : LoadPatExternalSym<i32, zextloadi16, LOAD16_U_I32>;
def : LoadPatExternalSym<i64, sextloadi8, LOAD8_S_I64>;
def : LoadPatExternalSym<i64, zextloadi8, LOAD8_U_I64>;
def : LoadPatExternalSym<i64, sextloadi16, LOAD16_S_I64>;
def : LoadPatExternalSym<i64, zextloadi16, LOAD16_U_I64>;
def : LoadPatExternalSym<i64, sextloadi32, LOAD32_S_I64>;
def : LoadPatExternalSym<i64, zextloadi32, LOAD32_U_I64>;


// Select extending loads with just a constant offset.
def : LoadPatOffsetOnly<i32, sextloadi8, LOAD8_S_I32>;
def : LoadPatOffsetOnly<i32, zextloadi8, LOAD8_U_I32>;
def : LoadPatOffsetOnly<i32, sextloadi16, LOAD16_S_I32>;
def : LoadPatOffsetOnly<i32, zextloadi16, LOAD16_U_I32>;

def : LoadPatOffsetOnly<i64, sextloadi8, LOAD8_S_I64>;
def : LoadPatOffsetOnly<i64, zextloadi8, LOAD8_U_I64>;
def : LoadPatOffsetOnly<i64, sextloadi16, LOAD16_S_I64>;
def : LoadPatOffsetOnly<i64, zextloadi16, LOAD16_U_I64>;
def : LoadPatOffsetOnly<i64, sextloadi32, LOAD32_S_I64>;
def : LoadPatOffsetOnly<i64, zextloadi32, LOAD32_U_I64>;

def : LoadPatGlobalAddrOffOnly<i32, sextloadi8, LOAD8_S_I32>;
def : LoadPatGlobalAddrOffOnly<i32, zextloadi8, LOAD8_U_I32>;
def : LoadPatGlobalAddrOffOnly<i32, sextloadi16, LOAD16_S_I32>;
def : LoadPatGlobalAddrOffOnly<i32, zextloadi16, LOAD16_U_I32>;
def : LoadPatGlobalAddrOffOnly<i64, sextloadi8, LOAD8_S_I64>;
def : LoadPatGlobalAddrOffOnly<i64, zextloadi8, LOAD8_U_I64>;
def : LoadPatGlobalAddrOffOnly<i64, sextloadi16, LOAD16_S_I64>;
def : LoadPatGlobalAddrOffOnly<i64, zextloadi16, LOAD16_U_I64>;
def : LoadPatGlobalAddrOffOnly<i64, sextloadi32, LOAD32_S_I64>;
def : LoadPatGlobalAddrOffOnly<i64, zextloadi32, LOAD32_U_I64>;

def : LoadPatExternSymOffOnly<i32, sextloadi8, LOAD8_S_I32>;
def : LoadPatExternSymOffOnly<i32, zextloadi8, LOAD8_U_I32>;
def : LoadPatExternSymOffOnly<i32, sextloadi16, LOAD16_S_I32>;
def : LoadPatExternSymOffOnly<i32, zextloadi16, LOAD16_U_I32>;
def : LoadPatExternSymOffOnly<i64, sextloadi8, LOAD8_S_I64>;
def : LoadPatExternSymOffOnly<i64, zextloadi8, LOAD8_U_I64>;
def : LoadPatExternSymOffOnly<i64, sextloadi16, LOAD16_S_I64>;
def : LoadPatExternSymOffOnly<i64, zextloadi16, LOAD16_U_I64>;
def : LoadPatExternSymOffOnly<i64, sextloadi32, LOAD32_S_I64>;
def : LoadPatExternSymOffOnly<i64, zextloadi32, LOAD32_U_I64>;

// Resolve "don't care" extending loads to zero-extending loads. This is
// somewhat arbitrary, but zero-extending is conceptually simpler.

// Select "don't care" extending loads with no constant offset.
def : LoadPatNoOffset<i32, extloadi8, LOAD8_U_I32>;
def : LoadPatNoOffset<i32, extloadi16, LOAD16_U_I32>;
def : LoadPatNoOffset<i64, extloadi8, LOAD8_U_I64>;
def : LoadPatNoOffset<i64, extloadi16, LOAD16_U_I64>;
def : LoadPatNoOffset<i64, extloadi32, LOAD32_U_I64>;

// Select "don't care" extending loads with a constant offset.
def : LoadPatImmOff<i32, extloadi8, regPlusImm, LOAD8_U_I32>;
def : LoadPatImmOff<i32, extloadi16, regPlusImm, LOAD16_U_I32>;
def : LoadPatImmOff<i64, extloadi8, regPlusImm, LOAD8_U_I64>;
def : LoadPatImmOff<i64, extloadi16, regPlusImm, LOAD16_U_I64>;
def : LoadPatImmOff<i64, extloadi32, regPlusImm, LOAD32_U_I64>;
def : LoadPatImmOff<i32, extloadi8, or_is_add, LOAD8_U_I32>;
def : LoadPatImmOff<i32, extloadi16, or_is_add, LOAD16_U_I32>;
def : LoadPatImmOff<i64, extloadi8, or_is_add, LOAD8_U_I64>;
def : LoadPatImmOff<i64, extloadi16, or_is_add, LOAD16_U_I64>;
def : LoadPatImmOff<i64, extloadi32, or_is_add, LOAD32_U_I64>;
def : LoadPatGlobalAddr<i32, extloadi8, LOAD8_U_I32>;
def : LoadPatGlobalAddr<i32, extloadi16, LOAD16_U_I32>;
def : LoadPatGlobalAddr<i64, extloadi8, LOAD8_U_I64>;
def : LoadPatGlobalAddr<i64, extloadi16, LOAD16_U_I64>;
def : LoadPatGlobalAddr<i64, extloadi32, LOAD32_U_I64>;
def : LoadPatExternalSym<i32, extloadi8, LOAD8_U_I32>;
def : LoadPatExternalSym<i32, extloadi16, LOAD16_U_I32>;
def : LoadPatExternalSym<i64, extloadi8, LOAD8_U_I64>;
def : LoadPatExternalSym<i64, extloadi16, LOAD16_U_I64>;
def : LoadPatExternalSym<i64, extloadi32, LOAD32_U_I64>;

// Select "don't care" extending loads with just a constant offset.
def : LoadPatOffsetOnly<i32, extloadi8, LOAD8_U_I32>;
def : LoadPatOffsetOnly<i32, extloadi16, LOAD16_U_I32>;
def : LoadPatOffsetOnly<i64, extloadi8, LOAD8_U_I64>;
def : LoadPatOffsetOnly<i64, extloadi16, LOAD16_U_I64>;
def : LoadPatOffsetOnly<i64, extloadi32, LOAD32_U_I64>;
def : LoadPatGlobalAddrOffOnly<i32, extloadi8, LOAD8_U_I32>;
def : LoadPatGlobalAddrOffOnly<i32, extloadi16, LOAD16_U_I32>;
def : LoadPatGlobalAddrOffOnly<i64, extloadi8, LOAD8_U_I64>;
def : LoadPatGlobalAddrOffOnly<i64, extloadi16, LOAD16_U_I64>;
def : LoadPatGlobalAddrOffOnly<i64, extloadi32, LOAD32_U_I64>;
def : LoadPatExternSymOffOnly<i32, extloadi8, LOAD8_U_I32>;
def : LoadPatExternSymOffOnly<i32, extloadi16, LOAD16_U_I32>;
def : LoadPatExternSymOffOnly<i64, extloadi8, LOAD8_U_I64>;
def : LoadPatExternSymOffOnly<i64, extloadi16, LOAD16_U_I64>;
def : LoadPatExternSymOffOnly<i64, extloadi32, LOAD32_U_I64>;


let Defs = [ARGUMENTS] in {

// Defines atomic and non-atomic stores, regular and truncating
class WebAssemblyStore<WebAssemblyRegClass rc, string Name, int Opcode> :
 I<(outs), (ins P2Align:$p2align, offset32_op:$off, I32:$addr, rc:$val), [],
   !strconcat(Name, "\t${off}(${addr})${p2align}, $val"), Opcode>;
// Basic store.
// Note: WebAssembly inverts SelectionDAG's usual operand order.
def STORE_I32  : WebAssemblyStore<I32, "i32.store", 0x36>;
def STORE_I64  : WebAssemblyStore<I64, "i64.store", 0x37>;
def STORE_F32  : WebAssemblyStore<F32, "f32.store", 0x38>;
def STORE_F64  : WebAssemblyStore<F64, "f64.store", 0x39>;

} // Defs = [ARGUMENTS]

// Select stores with no constant offset.
class StorePatNoOffset<ValueType ty, PatFrag node, I inst> :
  Pat<(node ty:$val, I32:$addr), (inst 0, 0, $addr, $val)>;

def : StorePatNoOffset<i32, store, STORE_I32>;
def : StorePatNoOffset<i64, store, STORE_I64>;
def : StorePatNoOffset<f32, store, STORE_F32>;
def : StorePatNoOffset<f64, store, STORE_F64>;

// Select stores with a constant offset.
class StorePatImmOff<ValueType ty, PatFrag storekind, PatFrag operand, I inst> :
  Pat<(storekind ty:$val, (operand I32:$addr, imm:$off)),
      (inst 0, imm:$off, $addr, ty:$val)>;

def : StorePatImmOff<i32, store, regPlusImm, STORE_I32>;
def : StorePatImmOff<i64, store, regPlusImm, STORE_I64>;
def : StorePatImmOff<f32, store, regPlusImm, STORE_F32>;
def : StorePatImmOff<f64, store, regPlusImm, STORE_F64>;
def : StorePatImmOff<i32, store, or_is_add, STORE_I32>;
def : StorePatImmOff<i64, store, or_is_add, STORE_I64>;
def : StorePatImmOff<f32, store, or_is_add, STORE_F32>;
def : StorePatImmOff<f64, store, or_is_add, STORE_F64>;

class StorePatGlobalAddr<ValueType ty, PatFrag storekind, I inst> :
  Pat<(storekind ty:$val, (regPlusGA I32:$addr,
                                     (WebAssemblywrapper tglobaladdr:$off))),
      (inst 0, tglobaladdr:$off, I32:$addr, ty:$val)>;
def : StorePatGlobalAddr<i32, store, STORE_I32>;
def : StorePatGlobalAddr<i64, store, STORE_I64>;
def : StorePatGlobalAddr<f32, store, STORE_F32>;
def : StorePatGlobalAddr<f64, store, STORE_F64>;

class StorePatExternalSym<ValueType ty, PatFrag storekind, I inst> :
  Pat<(storekind ty:$val, (add I32:$addr,
                               (WebAssemblywrapper texternalsym:$off))),
      (inst 0, texternalsym:$off, I32:$addr, ty:$val)>;
def : StorePatExternalSym<i32, store, STORE_I32>;
def : StorePatExternalSym<i64, store, STORE_I64>;
def : StorePatExternalSym<f32, store, STORE_F32>;
def : StorePatExternalSym<f64, store, STORE_F64>;

// Select stores with just a constant offset.
class StorePatOffsetOnly<ValueType ty, PatFrag storekind, I inst> :
  Pat<(storekind ty:$val, imm:$off),
      (inst 0, imm:$off, (CONST_I32 0), ty:$val)>;
def : StorePatOffsetOnly<i32, store, STORE_I32>;
def : StorePatOffsetOnly<i64, store, STORE_I64>;
def : StorePatOffsetOnly<f32, store, STORE_F32>;
def : StorePatOffsetOnly<f64, store, STORE_F64>;

class StorePatGlobalAddrOffOnly<ValueType ty, PatFrag storekind, I inst> :
  Pat<(storekind ty:$val, (WebAssemblywrapper tglobaladdr:$off)),
      (inst 0, tglobaladdr:$off, (CONST_I32 0), ty:$val)>;
def : StorePatGlobalAddrOffOnly<i32, store, STORE_I32>;
def : StorePatGlobalAddrOffOnly<i64, store, STORE_I64>;
def : StorePatGlobalAddrOffOnly<f32, store, STORE_F32>;
def : StorePatGlobalAddrOffOnly<f64, store, STORE_F64>;

class StorePatExternSymOffOnly<ValueType ty, PatFrag storekind, I inst> :
  Pat<(storekind ty:$val, (WebAssemblywrapper texternalsym:$off)),
      (inst 0, texternalsym:$off, (CONST_I32 0), ty:$val)>;
def : StorePatExternSymOffOnly<i32, store, STORE_I32>;
def : StorePatExternSymOffOnly<i64, store, STORE_I64>;
def : StorePatExternSymOffOnly<f32, store, STORE_F32>;
def : StorePatExternSymOffOnly<f64, store, STORE_F64>;


let Defs = [ARGUMENTS] in {

// Truncating store.
def STORE8_I32 : WebAssemblyStore<I32, "i32.store8", 0x3a>;
def STORE16_I32 : WebAssemblyStore<I32, "i32.store16", 0x3b>;
def STORE8_I64 : WebAssemblyStore<I64, "i64.store8", 0x3c>;
def STORE16_I64 : WebAssemblyStore<I64, "i64.store16", 0x3d>;
def STORE32_I64 : WebAssemblyStore<I64, "i64.store32", 0x3e>;

} // Defs = [ARGUMENTS]

// Select truncating stores with no constant offset.
def : StorePatNoOffset<i32, truncstorei8, STORE8_I32>;
def : StorePatNoOffset<i32, truncstorei16, STORE16_I32>;
def : StorePatNoOffset<i64, truncstorei8, STORE8_I64>;
def : StorePatNoOffset<i64, truncstorei16, STORE16_I64>;
def : StorePatNoOffset<i64, truncstorei32, STORE32_I64>;

// Select truncating stores with a constant offset.
def : StorePatImmOff<i32, truncstorei8, regPlusImm, STORE8_I32>;
def : StorePatImmOff<i32, truncstorei16, regPlusImm, STORE16_I32>;
def : StorePatImmOff<i64, truncstorei8, regPlusImm, STORE8_I64>;
def : StorePatImmOff<i64, truncstorei16, regPlusImm, STORE16_I64>;
def : StorePatImmOff<i64, truncstorei32, regPlusImm, STORE32_I64>;
def : StorePatImmOff<i32, truncstorei8, or_is_add, STORE8_I32>;
def : StorePatImmOff<i32, truncstorei16, or_is_add, STORE16_I32>;
def : StorePatImmOff<i64, truncstorei8, or_is_add, STORE8_I64>;
def : StorePatImmOff<i64, truncstorei16, or_is_add, STORE16_I64>;
def : StorePatImmOff<i64, truncstorei32, or_is_add, STORE32_I64>;

def : StorePatGlobalAddr<i32, truncstorei8, STORE8_I32>;
def : StorePatGlobalAddr<i32, truncstorei16, STORE16_I32>;
def : StorePatGlobalAddr<i64, truncstorei8, STORE8_I64>;
def : StorePatGlobalAddr<i64, truncstorei16, STORE16_I64>;
def : StorePatGlobalAddr<i64, truncstorei32, STORE32_I64>;
def : StorePatExternalSym<i32, truncstorei8, STORE8_I32>;
def : StorePatExternalSym<i32, truncstorei16, STORE16_I32>;
def : StorePatExternalSym<i64, truncstorei8, STORE8_I64>;
def : StorePatExternalSym<i64, truncstorei16, STORE16_I64>;
def : StorePatExternalSym<i64, truncstorei32, STORE32_I64>;

// Select truncating stores with just a constant offset.
def : StorePatOffsetOnly<i32, truncstorei8, STORE8_I32>;
def : StorePatOffsetOnly<i32, truncstorei16, STORE16_I32>;
def : StorePatOffsetOnly<i64, truncstorei8, STORE8_I64>;
def : StorePatOffsetOnly<i64, truncstorei16, STORE16_I64>;
def : StorePatOffsetOnly<i64, truncstorei32, STORE32_I64>;
def : StorePatGlobalAddrOffOnly<i32, truncstorei8, STORE8_I32>;
def : StorePatGlobalAddrOffOnly<i32, truncstorei16, STORE16_I32>;
def : StorePatGlobalAddrOffOnly<i64, truncstorei8, STORE8_I64>;
def : StorePatGlobalAddrOffOnly<i64, truncstorei16, STORE16_I64>;
def : StorePatGlobalAddrOffOnly<i64, truncstorei32, STORE32_I64>;
def : StorePatExternSymOffOnly<i32, truncstorei8, STORE8_I32>;
def : StorePatExternSymOffOnly<i32, truncstorei16, STORE16_I32>;
def : StorePatExternSymOffOnly<i64, truncstorei8, STORE8_I64>;
def : StorePatExternSymOffOnly<i64, truncstorei16, STORE16_I64>;
def : StorePatExternSymOffOnly<i64, truncstorei32, STORE32_I64>;

let Defs = [ARGUMENTS] in {

// Current memory size.
def MEM_SIZE_I32 : I<(outs I32:$dst), (ins i32imm:$flags),
                     [(set I32:$dst, (int_wasm_mem_size (i32 imm:$flags)))],
                     "mem.size\t$dst, $flags", 0x3f>,
                   Requires<[HasAddr32]>;
def CURRENT_MEMORY_I32 : I<(outs I32:$dst), (ins i32imm:$flags),
                           [],
                           "current_memory\t$dst", 0x3f>,
                         Requires<[HasAddr32]>;

// Grow memory.
def MEM_GROW_I32 : I<(outs I32:$dst), (ins i32imm:$flags, I32:$delta),
                     [(set I32:$dst,
                           (int_wasm_mem_grow (i32 imm:$flags), I32:$delta))],
                     "mem.grow\t$dst, $flags, $delta", 0x3f>,
                   Requires<[HasAddr32]>;
def GROW_MEMORY_I32 : I<(outs I32:$dst), (ins i32imm:$flags, I32:$delta),
                        [],
                        "grow_memory\t$dst, $delta", 0x40>,
                      Requires<[HasAddr32]>;

} // Defs = [ARGUMENTS]

def : Pat<(int_wasm_current_memory),
          (CURRENT_MEMORY_I32 0)>;
def : Pat<(int_wasm_grow_memory I32:$delta),
          (GROW_MEMORY_I32 0, $delta)>;
