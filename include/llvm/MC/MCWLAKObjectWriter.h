//===- llvm/MC/MCWLAKObjectWriter.h - WLAK Object Writer --------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_MC_MCWLAKOBJECTWRITER_H
#define LLVM_MC_MCWLAKOBJECTWRITER_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/MC/MCExpr.h"
#include "llvm/MC/MCObjectWriter.h"
#include "llvm/MC/MCSection.h"
#include "llvm/MC/MCSymbol.h"
#include "llvm/MC/StringTableBuilder.h"
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

namespace llvm {

class MCWLAKObjectWriter;

class MCWLAKObjectTargetWriter : public MCObjectTargetWriter {
public:
  virtual ~MCWLAKObjectTargetWriter() = default;

  Triple::ObjectFormatType getFormat() const override {
    return Triple::WLAK;
  }

  static bool classof(const MCObjectTargetWriter *W) {
    return W->getFormat() == Triple::WLAK;
  }
};

namespace WLAK {
enum {
  FREE = 0,
  FORCED = 1,
  OVERWRITE = 2,
  HEADER = 3,
  SEMIFREE = 4,
  ABSOLUTE = 5,
  RAM = 6,
  SUPERFREE = 7
};
} // namespace WLAK

class MCWLAKCalcStackEntry {
  unsigned Type;
  unsigned Sign;
  // Source: wladx/wlalink/defines.h
  enum {
    VALUE = 0, OPERATOR = 1, STRING = 2, STACK = 4
  };
  union {
    double Value;
    const MCSymbol *Symbol;
  };
  MCWLAKCalcStackEntry(double Imm)
    : Type(VALUE), Sign(0), Value(Imm) {};
  MCWLAKCalcStackEntry(unsigned Op)
    : Type(OPERATOR), Sign(0), Value((double)Op) {};
  MCWLAKCalcStackEntry(const MCSymbol &Symbol, unsigned Sign)
    : Type(STRING), Sign(Sign), Symbol(&Symbol) {};

public:
  static MCWLAKCalcStackEntry createImm(int Imm) {
    return MCWLAKCalcStackEntry((double)Imm);
  }
  static MCWLAKCalcStackEntry createOp(unsigned Op) {
    return MCWLAKCalcStackEntry(Op);
  }
  static MCWLAKCalcStackEntry createSymb(const MCSymbol &Symbol,
                                       bool Invert = false) {
    return MCWLAKCalcStackEntry(Symbol, Invert ? 1 : 0);
  }
  enum {
    OP_ADD         =  0,
    OP_SUB         =  1,
    OP_MUL         =  2,
    OP_OR          =  5,
    OP_AND         =  6,
    OP_DIVIDE      =  7,
    OP_POWER       =  8,
    OP_SHIFT_LEFT  =  9,
    OP_SHIFT_RIGHT = 10,
    OP_MODULO      = 11,
    OP_XOR         = 12,
    OP_LOW_BYTE    = 13,
    OP_HIGH_BYTE   = 14
  };
  void write(MCAssembler &Asm, MCWLAKObjectWriter &Writer) const;
};

class MCWLAKRelocationEntry {
protected:
  const MCSection *Section;
  unsigned Type;
  unsigned FileID;
  unsigned LineNumber;
  unsigned Offset;

public:
  MCWLAKRelocationEntry(const MCSection &Section, unsigned Type,
                      unsigned FileID, unsigned LineNumber,
                      unsigned Offset)
    : Section(&Section), Type(Type), FileID(FileID),
      LineNumber(LineNumber), Offset(Offset) {};

  const MCSection &getSection() {
    return *Section;
  }

  virtual ~MCWLAKRelocationEntry() {}
  enum {
    DIRECT_8BIT, DIRECT_16BIT, DIRECT_24BIT,
    RELATIVE_8BIT, RELATIVE_16BIT
  };
};

class MCWLAKComplexRelocationEntry : public MCWLAKRelocationEntry {
protected:
  std::vector<MCWLAKCalcStackEntry> Stack;

public:
  MCWLAKComplexRelocationEntry(const MCSection &Section, unsigned Type,
                             unsigned FileID, unsigned LineNumber,
                             unsigned Offset)
    : MCWLAKRelocationEntry(Section, Type, FileID, LineNumber, Offset) {};

  void addImm(int Value) {
    Stack.push_back(MCWLAKCalcStackEntry::createImm(Value));
  }
  void addOp(unsigned Op) {
    Stack.push_back(MCWLAKCalcStackEntry::createOp(Op));
  }
  void addSymb(const MCSymbol &Symbol) {
    Stack.push_back(MCWLAKCalcStackEntry::createSymb(Symbol));
  }

  void write(MCAssembler &Asm, MCWLAKObjectWriter &Writer, unsigned ID) const;
};

class MCWLAKSimpleRelocationEntry : public MCWLAKRelocationEntry {
protected:
  const MCSymbol *Symbol;

public:
  MCWLAKSimpleRelocationEntry(const MCSection &Section, unsigned Type,
                            unsigned FileID, unsigned LineNumber,
                            unsigned Offset, const MCSymbol &Symbol)
    : MCWLAKRelocationEntry(Section, Type, FileID, LineNumber, Offset),
      Symbol(&Symbol) {};

  void write(MCAssembler &Asm, MCWLAKObjectWriter &Writer) const;
};

class MCWLAKObjectWriter : public MCObjectWriter {
protected:

  /// The target specific ELF writer instance.
  std::unique_ptr<MCWLAKObjectTargetWriter> TW;

  static bool isFixupKindPCRel(const MCAssembler &Asm, unsigned Kind);

  std::vector<MCWLAKSimpleRelocationEntry> SimpleRelocations;
  std::vector<MCWLAKComplexRelocationEntry> ComplexRelocations;

  // Maps MCSection to WLAK section ID.
  llvm::DenseMap<const MCSection *, unsigned> SectionIDMap;

  // Symbol information.
  struct SymbolInfo {
    bool Exported;
    bool Private;
    SymbolInfo() {}
  };
  DenseMap<const MCSymbol *, SymbolInfo> SymbolInfoMap;

  // If we have symbols without file or line number information, they
  // are assigned this file ID. Set to 0 if no such symbols are
  // encountered, in which case this "unknown" file is not emitted to
  // the source file list.
  unsigned UnknownFileID;
  unsigned NextSourceID;

  SmallDenseMap<unsigned, unsigned> BufferIDMap;
  SmallDenseMap<unsigned, const char*> SourceFilenameMap;

  std::pair<unsigned, unsigned>
  getFileAndLine(const MCAssembler &Asm, const MCFixup &Fixup);
  void getSections(MCAssembler &Asm, std::vector<const MCSection*> &Sections);
  void enumerateSections(MCAssembler &Asm, const MCAsmLayout &Layout);

public:

  raw_pwrite_stream &OS;
  support::endian::Writer W;

  MCWLAKObjectWriter(std::unique_ptr<MCWLAKObjectTargetWriter> TW,
                     raw_pwrite_stream &OS)
    : TW{std::move(TW)}, UnknownFileID{0}, NextSourceID{0}, OS{OS},
      W(OS, support::big) {};
  ~MCWLAKObjectWriter() override = default;

  unsigned getSectionID(const MCSection &Section) const;
  bool symbolExists(const MCSymbol &Symb) const;
  bool isSymbolPrivate(const MCSymbol &Symb) const;

  /// \brief Record a relocation entry.
  ///
  /// This routine is called by the assembler after layout and relaxation, and
  /// post layout binding. The implementation is responsible for storing
  /// information about the relocation so that it can be emitted during
  /// WriteObject().
  void recordRelocation(MCAssembler &Asm, const MCAsmLayout &Layout,
                        const MCFragment *Fragment,
                        const MCFixup &Fixup, MCValue Target,
                        uint64_t &FixedValue) override;

  /// \brief Perform any late binding of symbols (for example, to assign symbol
  /// indices for use when generating relocations).
  ///
  /// This routine is called by the assembler after layout and relaxation is
  /// complete.
  virtual void executePostLayoutBinding(MCAssembler &Asm,
                                        const MCAsmLayout &Layout) override;
  void writeSection(MCAssembler &Asm,
                    const MCAsmLayout &Layout,
                    const MCSection &Section);

  void writeSymbolName(MCAssembler &Asm,
                       const MCSymbol &Symbol);

  void writeSymbol(MCAssembler &Asm,
                   const MCAsmLayout &Layout,
                   const MCSymbol &Symbol);

  void writeSymbolTable(MCAssembler &Asm,
                        const MCAsmLayout &Layout);

  void writeSourceFiles(MCAssembler &Asm, const MCAsmLayout &Layout);

  uint64_t writeObject(MCAssembler &Asm, const MCAsmLayout &Layout) override;
};

/// Construct a new WLAK writer instance.
///
/// This routine takes ownership of the target writer subclass.
///
/// \param TW - The target specific WLAK writer subclass.
/// \param OS - The stream to write to.
/// \returns The constructed object writer.
std::unique_ptr<MCObjectWriter>
createWLAKObjectWriter(std::unique_ptr<MCWLAKObjectTargetWriter> TW,
                       raw_pwrite_stream &OS);

} // end namespace llvm

#endif // LLVM_MC_MCWLAKOBJECTWRITER_H
