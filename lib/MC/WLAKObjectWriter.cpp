//===- lib/MC/WLAKObjectWriter.cpp - WLAK File Writer ---------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements WLAK object file writer information.
//
//===----------------------------------------------------------------------===//

#include "llvm/MC/MCAssembler.h"
#include "llvm/MC/MCAsmLayout.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCExpr.h"
#include "llvm/MC/MCObjectWriter.h"
#include "llvm/MC/MCSection.h"
#include "llvm/MC/MCSymbol.h"
#include "llvm/MC/MCValue.h"
#include "llvm/MC/MCWLAKObjectWriter.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SourceMgr.h"

using namespace llvm;

#define DEBUG_TYPE "mc"

namespace llvm {
  namespace C65 {
    enum Fixups {
      // Constants shifted by X to fit in an 8-bit register.
      FK_C65_8 = FirstTargetFixupKind,
      FK_C65_8s8,
      FK_C65_8s16,
      FK_C65_8s24,
      FK_C65_8s32,
      FK_C65_8s40,
      FK_C65_8s48,
      FK_C65_8s56,
      // Constants shifted by X to fit in a 16-bit register.
      FK_C65_16,
      FK_C65_16s16,
      FK_C65_16s32,
      FK_C65_16s48,
      // 24-bit fixup.
      FK_C65_24,

      // Marker
      LastTargetFixupKind,
      NumTargetFixupKinds = LastTargetFixupKind - FirstTargetFixupKind
    };

    static inline bool isFixup8Bit(int FK) {
      return FK >= FK_C65_8 && FK <= FK_C65_8s56;
    }
    static inline int get8BitFixupShiftAmt(int FK) {
      return (FK - FK_C65_8) << 3;
    }
    static inline bool isFixup16Bit(int FK) {
      return FK >= FK_C65_16 && FK <= FK_C65_16s48;
    }
    static inline int get16BitFixupShiftAmt(int FK) {
      return (FK - FK_C65_16) << 4;
    }
  } // end namespace C65
} // end namespace llvm

// MCWLAKCalcStackEntry Impl

void MCWLAKCalcStackEntry::write(MCAssembler &Asm,
                                 MCWLAKObjectWriter &Writer) const {
  Writer.W.write<uint8_t>(Type);
  Writer.W.write<uint8_t>(Sign);
  if (Type == VALUE || Type == OPERATOR) {
    const uint64_t *X = (const uint64_t *)(&Value);
    Writer.W.write<uint64_t>(*X);
  } else {
    Writer.writeSymbolName(Asm, *Symbol);
    Writer.W.write<uint8_t>(0);
  }
}

// MCWLAKComplexRelocationEntry Impl

void MCWLAKComplexRelocationEntry::write(MCAssembler &Asm,
                                       MCWLAKObjectWriter &Writer,
                                       unsigned ID) const {
  Writer.W.write<uint32_t>(ID);
  if (Type == MCWLAKRelocationEntry::DIRECT_8BIT)
    Writer.W.write<uint8_t>(0x0);
  else if (Type == MCWLAKRelocationEntry::DIRECT_16BIT)
    Writer.W.write<uint8_t>(0x1);
  else if (Type == MCWLAKRelocationEntry::DIRECT_24BIT)
    Writer.W.write<uint8_t>(0x2);
  else if (Type == MCWLAKRelocationEntry::RELATIVE_8BIT)
    Writer.W.write<uint8_t>(0x80);
  else /* Type == MCWLAKRelocationEntry::RELATIVE_16BIT */
    Writer.W.write<uint8_t>(0x81);
  Writer.W.write<uint8_t>(Writer.getSectionID(*Section));
  Writer.W.write<uint8_t>(FileID);
  Writer.W.write<uint8_t>(Stack.size());
  Writer.W.write<uint8_t>(0);
  Writer.W.write<uint32_t>(Offset);
  Writer.W.write<uint32_t>(LineNumber);
  for (const MCWLAKCalcStackEntry &E : Stack)
    E.write(Asm, Writer);
}

// MCWLAKSimpleRelocationEntry Impl

void MCWLAKSimpleRelocationEntry::write(MCAssembler &Asm,
                                      MCWLAKObjectWriter &Writer) const {
  Writer.writeSymbolName(Asm, *Symbol);
  Writer.W.write<uint8_t>(0);
  if (Type == MCWLAKRelocationEntry::DIRECT_8BIT)
    Writer.W.write<uint8_t>(0x2);
  else if (Type == MCWLAKRelocationEntry::DIRECT_16BIT)
    Writer.W.write<uint8_t>(0x0);
  else if (Type == MCWLAKRelocationEntry::DIRECT_24BIT)
    Writer.W.write<uint8_t>(0x3);
  else if (Type == MCWLAKRelocationEntry::RELATIVE_8BIT)
    Writer.W.write<uint8_t>(0x1);
  else /* Type == MCWLAKRelocationEntry::RELATIVE_16BIT */
    Writer.W.write<uint8_t>(0x4);
  Writer.W.write<uint8_t>(Writer.getSectionID(*Section));
  Writer.W.write<uint8_t>(FileID);
  Writer.W.write<uint32_t>(LineNumber);
  Writer.W.write<uint32_t>(Offset);
}

// MCWLAKObjectWriter Impl

static unsigned getRelocType(const MCFixup &Fixup) {
  switch((unsigned)Fixup.getKind()) {
  default:
    llvm_unreachable("Unimplemented fixup -> relocation");
  case FK_PCRel_1:
    return MCWLAKRelocationEntry::RELATIVE_8BIT;
  case FK_PCRel_2:
    return MCWLAKRelocationEntry::RELATIVE_16BIT;
  case FK_Data_1:
  case C65::FK_C65_8:
  case C65::FK_C65_8s8:
  case C65::FK_C65_8s16:
  case C65::FK_C65_8s24:
  case C65::FK_C65_8s32:
  case C65::FK_C65_8s40:
  case C65::FK_C65_8s48:
  case C65::FK_C65_8s56:
    return MCWLAKRelocationEntry::DIRECT_8BIT;
  case FK_Data_2:
  case C65::FK_C65_16:
  case C65::FK_C65_16s16:
  case C65::FK_C65_16s32:
  case C65::FK_C65_16s48:
    return MCWLAKRelocationEntry::DIRECT_16BIT;
  case FK_Data_4:
  case C65::FK_C65_24:
    return MCWLAKRelocationEntry::DIRECT_24BIT;
  }
}

static unsigned getFixupShiftAmt(const MCFixup &Fixup) {
  int Kind = Fixup.getKind();
  if (C65::isFixup8Bit(Kind))
    return C65::get8BitFixupShiftAmt(Kind);
  else if (C65::isFixup16Bit(Kind))
    return C65::get16BitFixupShiftAmt(Kind);
  else
    return 0;
}

std::pair<unsigned, unsigned>
MCWLAKObjectWriter::getFileAndLine(const MCAssembler &Asm,
                                 const MCFixup &Fixup) {
  MCContext &Ctx = Asm.getContext();
  const SourceMgr *SrcMgr = Ctx.getSourceManager();
  if (!SrcMgr) {
    if (!UnknownFileID)
      UnknownFileID = NextSourceID++;
    return std::make_pair(UnknownFileID, 0);
  }

  SMLoc Loc = Fixup.getLoc();
  if (!Loc.isValid()) {
    if (!UnknownFileID)
      UnknownFileID = NextSourceID++;
    return std::make_pair(UnknownFileID, 0);
  }

  unsigned BufferID = SrcMgr->FindBufferContainingLoc(Loc);
  unsigned SourceID;

  // See if we have already assigned an ID for this buffer.
  auto I = BufferIDMap.find(BufferID);
  if (I != BufferIDMap.end()) {
    SourceID = I->second;
  } else {
    SourceID = NextSourceID++;
    BufferIDMap[BufferID] = SourceID;
  }
  unsigned LineNumber = SrcMgr->FindLineNumber(Loc, BufferID);
  return std::make_pair(SourceID, LineNumber);
}

void MCWLAKObjectWriter::recordRelocation(MCAssembler &Asm,
                                        const MCAsmLayout &Layout,
                                        const MCFragment *Fragment,
                                        const MCFixup &Fixup,
                                        MCValue Target,
                                        uint64_t &FixedValue) {
  const MCSection *Section = Fragment->getParent();
  std::pair<unsigned, unsigned> FileAndLine = getFileAndLine(Asm, Fixup);
  unsigned FileID = FileAndLine.first;
  unsigned LineNumber = FileAndLine.second;

  unsigned C = Target.getConstant();
  unsigned Offset = Layout.getFragmentOffset(Fragment) + Fixup.getOffset();
  unsigned Type = getRelocType(Fixup);
  unsigned ShiftAmt = getFixupShiftAmt(Fixup);

  const MCSymbolRefExpr *RefA = Target.getSymA();
  const MCSymbolRefExpr *RefB = Target.getSymB();
  const MCSymbol &SymA = RefA->getSymbol();

  if (ShiftAmt || RefB || C) {
    // MCWLAK supports arbitrary calculations for relocations using a
    // stack-based language.
    MCWLAKComplexRelocationEntry Rel(*Section, Type, FileID, LineNumber, Offset);
    Rel.addSymb(SymA);
    if (RefB) {
      assert(RefB->getKind() == MCSymbolRefExpr::VK_None &&
             "Should not have constructed this");

      const MCSymbol &SymB = RefB->getSymbol();
      assert(!SymB.isAbsolute() && "Should have been folded");

      Rel.addSymb(RefB->getSymbol());
      Rel.addOp(MCWLAKCalcStackEntry::OP_SUB);
    }
    if (C) {
      Rel.addImm(C);
      Rel.addOp(MCWLAKCalcStackEntry::OP_ADD);
    }
    if (ShiftAmt) {
      Rel.addImm(ShiftAmt);
      Rel.addOp(MCWLAKCalcStackEntry::OP_SHIFT_RIGHT);
    }
    ComplexRelocations.push_back(Rel);
  } else {
    MCWLAKSimpleRelocationEntry Rel(*Section, Type, FileID, LineNumber,
                                  Offset, SymA);
    SimpleRelocations.push_back(Rel);
  }
}

void MCWLAKObjectWriter::executePostLayoutBinding(MCAssembler &Asm,
                                                const MCAsmLayout &Layout) {
  for (const MCSymbol &SD : Asm.symbols()) {
    SymbolInfo SI;
    SI.Exported = SD.isInSection() && !SD.getName().empty();
    SI.Private = SD.isDefined() && !SD.isExternal();
    SymbolInfoMap[&SD] = SI;
  }
}

void MCWLAKObjectWriter::writeSection(MCAssembler &Asm,
                                      const MCAsmLayout &Layout,
                                      const MCSection &Section) {
  unsigned Size = Layout.getSectionFileSize(&Section);
  StringRef SectionName;
  SectionKind Kind = Section.getKind();

  if (Kind.isText())
    SectionName = StringRef("TEXT");
  else if (Kind.isData())
    SectionName = StringRef("DATA_REL");
  // else if (Kind.isDataRelLocal())
  //   SectionName = StringRef("DATA_REL_LOCAL");
  // else if (Kind.isDataNoRel())
  //   SectionName = StringRef("DATA_NOREL");
  else
    SectionName = StringRef("UNKNOWN");
  OS << SectionName;
  // String terminator decides section constraint
  W.write<uint8_t>(0); // 0 - FREE, 7 - SUPERFREE
  W.write<uint8_t>(getSectionID(Section)); // Section ID
  W.write<uint8_t>(1); // FileID
  W.write<uint32_t>(Size);
  W.write<uint32_t>(1); // Alignment
  Asm.writeSectionData(OS, &Section, Layout);
  W.write<uint8_t>(0); // List file information, 0 - not present
}

// For the WLAK file type, we need to add underscores to names that
// are not external and not guaranteed to be unique across all object
// files. This function serves this purpose.
//
void MCWLAKObjectWriter::writeSymbolName(MCAssembler &Asm,
                                       const MCSymbol &Symbol) {
  // Append the file name to private symbols. We can't use underscores
  // here, since they are section-private and does not resolve across
  // sections.
  if (isSymbolPrivate(Symbol)) {
    ArrayRef<std::string> FileNames = Asm.getFileNames();
    if (FileNames.begin() != FileNames.end()) {
      std::string Name = *FileNames.begin();
      for (auto I = Name.begin(), E = Name.end(); I != E; ++I) {
        if (*I == '_')
          OS << '~';
        else
          OS << *I;
      }
      OS << '~';
    } else {
      // With no file name defined, prepend an underscore.
      OS << '_';
    }
  }
  OS << Symbol.getName();
}

void MCWLAKObjectWriter::writeSymbol(MCAssembler &Asm,
                                   const MCAsmLayout &Layout,
                                   const MCSymbol &Symbol) {
  writeSymbolName(Asm, Symbol);
  // String terminator decides type
  W.write<uint8_t>(0); // 0 - label, 1 - symbol, 2 - breakpoint
  W.write<uint8_t>(getSectionID(Symbol.getSection())); // Section ID
  W.write<uint8_t>(1); // File ID
  W.write<uint32_t>(0); // Line number

  // Write symbol offset
  uint64_t Val;
  if (!Layout.getSymbolOffset(Symbol, Val))
    report_fatal_error("expected absolute expression");
  W.write<uint32_t>(Val);
}

void MCWLAKObjectWriter::writeSymbolTable(MCAssembler &Asm,
                                        const MCAsmLayout &Layout) {
  unsigned NumExportedSymbols = 0;

  for (auto I : SymbolInfoMap) {
    if (I.second.Exported)
      ++NumExportedSymbols;
  }

  W.write<uint32_t>(NumExportedSymbols);

  for (auto I : SymbolInfoMap) {
    if (I.second.Exported)
      writeSymbol(Asm, Layout, *I.first);
  }
}

void MCWLAKObjectWriter::enumerateSections(MCAssembler &Asm,
                                           const MCAsmLayout &Layout) {
  unsigned NextID = 1;
  for (const MCSection &Section : Asm)
    SectionIDMap[&Section] = NextID++;
}

unsigned MCWLAKObjectWriter::getSectionID(const MCSection &Section) const {
  return SectionIDMap.lookup(&Section);
}

bool MCWLAKObjectWriter::symbolExists(const MCSymbol &Symb) const {
  return SymbolInfoMap.find(&Symb) != SymbolInfoMap.end();
}


bool MCWLAKObjectWriter::isSymbolPrivate(const MCSymbol &Symb) const {
  assert (symbolExists(Symb));
  return Symb.isTemporary() || SymbolInfoMap.lookup(&Symb).Private;
}

void MCWLAKObjectWriter::writeSourceFiles(MCAssembler &Asm,
                                        const MCAsmLayout &Layout) {
  // If there is no buffer information, try to use the file names
  // supplied in Asm.
  if (BufferIDMap.empty()) {
    // In case there are no symbols, UnknownFileID will be empty even
    // here.
    if (!UnknownFileID)
      UnknownFileID = NextSourceID++;

    ArrayRef<std::string> FileNames = Asm.getFileNames();
    if (FileNames.begin() != FileNames.end() &&
        FileNames.begin() + 1 == FileNames.end()) {
      // There is only one file name, use it as the "unknown file".
      W.write<uint32_t>(1);
      OS << *FileNames.begin() << '\0';
      W.write<uint8_t>(UnknownFileID);
      return;
    }
  }

  MCContext &Ctx = Asm.getContext();
  const SourceMgr *SrcMgr = Ctx.getSourceManager();
  if (UnknownFileID)
    W.write<uint32_t>(BufferIDMap.size() + 1);
  else
    W.write<uint32_t>(BufferIDMap.size());

  for (auto I = BufferIDMap.begin(), E = BufferIDMap.end(); I != E; ++I) {
    unsigned BufferID = I->first;
    std::string Identifier;
    if (SrcMgr) {
      const MemoryBuffer *MemBuff = SrcMgr->getMemoryBuffer(BufferID);
      if (MemBuff && !MemBuff->getBufferIdentifier().empty())
        Identifier = MemBuff->getBufferIdentifier().str();
    }
    if (!Identifier.empty())
      OS << Identifier;
    else
      OS << "anonymous file " << BufferID;
    OS << '\0';
    W.write<uint8_t>(I->second);
  }
  if (UnknownFileID) {
    OS << "unknown file" << '\0';
    W.write<uint8_t>(UnknownFileID);
  }
}

uint64_t MCWLAKObjectWriter::writeObject(MCAssembler &Asm,
                                         const MCAsmLayout &Layout) {
  uint64_t StartOffset = W.OS.tell();

  enumerateSections(Asm, Layout);

  // Header
  W.write<uint8_t>('W');
  W.write<uint8_t>('L');
  W.write<uint8_t>('A');
  W.write<uint8_t>('V'); // 'WLAV'

  // Write the name of the source files, if available.
  writeSourceFiles(Asm, Layout);

  // Write exported definitions
  W.write<uint32_t>(0);

  // Write labels, symbols and breakpoints. Also creates a table
  // outlining which symbols are marked as private.
  writeSymbolTable(Asm, Layout);

  // Write "Outside references"
  W.write<uint32_t>(SimpleRelocations.size());
  for (const MCWLAKSimpleRelocationEntry &Rel : SimpleRelocations) {
    Rel.write(Asm, *this);
  }

  // Write "Pending calculations"
  W.write<uint32_t>(ComplexRelocations.size());
  unsigned CalcID = 1;
  for (const MCWLAKComplexRelocationEntry &Rel : ComplexRelocations) {
    Rel.write(Asm, *this, CalcID++);
  }

  // Write data sections
  std::vector<const MCSection*> Sections;
  getSections(Asm, Sections);
  for (const MCSection *Section : Sections) {
    writeSection(Asm, Layout, *Section);
  }
  return W.OS.tell() - StartOffset;
}

void
MCWLAKObjectWriter::getSections(MCAssembler &Asm,
                                std::vector<const MCSection*> &Sections) {
  for (MCAssembler::iterator IT = Asm.begin(),
         IE = Asm.end(); IT != IE; ++IT) {
    Sections.push_back(&(*IT));
  }
}

std::unique_ptr<MCObjectWriter>
llvm::createWLAKObjectWriter(std::unique_ptr<MCWLAKObjectTargetWriter> TW,
                             raw_pwrite_stream &OS) {
  return llvm::make_unique<MCWLAKObjectWriter>(std::move(TW), OS);
}
