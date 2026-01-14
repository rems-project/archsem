# Isla DSL → ArchSem TOML Translation

## Overview

The `convert_isla` tool transforms symbolic Isla TOML files into concrete ArchSem TOML files suitable for execution in the ArchSem litmus test framework.

## Architecture

The conversion process is handled by four main modules:

1. **Input Parser** (`input_parser.ml`)
   - Parses Isla TOML format
   - Extracts threads, sections, and page table DSL
   - Supports both `reset` and `init` register sections

2. **Page Tables** (`page_tables.ml`)
   - Processes page table setup DSL
   - Generates multi-level page table structures
   - Installs identity mappings for code and data
   - Manages descriptor attributes (code vs data)

3. **Output Emitter** (`output_emitter.ml`)
   - Generates ArchSem TOML output
   - Emits memory regions (code, data, page tables)
   - Creates register initialization blocks
   - Translates outcome assertions

4. **Converter** (`converter.ml`)
   - Orchestrates the conversion process
   - Manages symbol tables and allocators
   - Coordinates VA/PA mapping

## Translation Summary

| Isla DSL | ArchSem TOML | Notes |
|----------|--------------|-------|
| `arch = "AArch64"` | `arch = "AArch64"` | Architecture name |
| `symbolic = ["x", "y"]` | `# x = 0x...` (comment) | Symbolic addresses allocated |
| `[thread.0] code = "..."` | `[[memory]] data=[opcodes]` | Assembly → encoded instructions |
| `[thread.0.reset]` or `[thread.0.init]` | `[[registers]] R0 = 0x...` | Register initialization |
| `page_table_setup = "..."` | `[[memory]]` entries (PT) | Page table entries |
| `[section.name]` | `[[memory]]` (code) | Exception handlers |
| `[final] assertion = ...` | `[[outcome]]` | Outcome assertions |
| *(implicit)* | `[[termCond]] _PC = <end>` | Termination condition |

---

## Address Allocation

### Virtual Addresses (VA)
- **Start**: `0x40_0000_0000` (256 GB offset)
- **Allocation**: Page-aligned (4 KB = `0x1000`)
- **Usage**: Symbolic variables, thread code (when not identity-mapped)

Example:
```
x     = 0x4000000000
y     = 0x4000001000
code_0 = 0x4000002000
```

### Physical Addresses (PA)
- **Page Tables**: Start at root table (allocated dynamically, typically ~`0x80000`)
- **Data**: Allocated after page tables
- **Code**: Either identity-mapped or allocated separately

Example:
```
Root Table:  0x80000
PA symbols:  0x81000, 0x82000, ...
Code:        0x2000 (identity-mapped) or allocated
```

### Symbolic Mapping Header
Debug comments show VA→PA mappings in output:

```toml
# Symbolic Variable Mapping:
# x = 0x4000000000 (mapped to PA pa1=0x81000)
# y = 0x4000001000 (mapped to PA pa2=0x82000)
```

---

## Page Table DSL Translation

### Identity Mapping
```
Isla DSL:  identity 0x1000 with code;
Output:    [[memory]] entries with executable descriptors
```

The converter:
1. Creates a valid L3 page descriptor
2. Installs mapping at VA=PA=0x1000
3. Uses code descriptor (readable from EL0/EL1, executable): `0x6C3`

### VA → PA Mapping
```
Isla DSL:  x |-> pa1;
Process:   1. Allocate VA for 'x' (e.g., 0x4000000000)
           2. Allocate PA for 'pa1' (e.g., 0x81000)
           3. Install 4-level page table entries (L0→L1→L2→L3)
Output:    Multiple [[memory]] blocks for each PT level
```

### Variant Mappings
```
Isla DSL:  x ?-> invalid at level 2;
Process:   Install invalid descriptor (all zeros)
Purpose:   Test translation fault handling
```

### Custom Tables
```
Isla DSL:  s1table custom 0x280000 {
             x |-> pa1;
           }
Process:   1. Register table at fixed address 0x280000
           2. Process mappings within that table context
```

---

## Code Translation

Assembly instructions are encoded to AArch64 opcodes:

### Input (Isla)
```toml
[thread.0]
code = """
    STR X0,[X1]
    DMB SY
    LDR X2,[X3]
"""
```

### Output (ArchSem)
```toml
[[memory]] # Code 0 (PA=0x2000)
base = 0x2000
size = 12
data = [0xf9000020, 0xd5033fbf, 0xf9400062]
```

**Details**:
- Each instruction = 4 bytes (32 bits)
- Size = number of instructions × 4
- `_PC` in `[[registers]]` = code base address
- `_PC` in `[[termCond]]` = base + size

### Exception Handlers

```toml
# Input
[section.thread0_el1_handler]
address = "0x1400"
code = "MOV X2,#0\nERET"

# Output
[[memory]] # Section thread0_el1_handler (PA=0x1400)
base = 0x1400
size = 8
data = [0xd2800002, 0xd69f03e0]
```

If handler doesn't end with `ERET`, the termination condition uses the handler's end address.

---

## Register Initialization

### Expression Evaluation

Both `reset` and `init` sections support symbolic expressions:

```toml
# Input
[thread.0.init]
X1 = "x"                              # Symbolic variable → VA
X2 = "pa1"                            # Physical address
X3 = "pte3(x, page_table_base)"       # Calculate PTE address
X4 = "0x1000"                         # Literal hex
PSTATE.EL = "0b01"                    # Exception level

# Output
[[registers]] # 0
_PC = 0x2000
R1 = 0x4000000000    # Resolved VA of 'x'
R2 = 0x81000         # Resolved PA of 'pa1'
R3 = 0x80ff8         # Calculated PTE address
R4 = 0x1000
PSTATE = { "EL" = 0b01, "SP" = 0b1 }
```

### Supported Functions

| Function | Example | Result |
|----------|---------|--------|
| Symbolic ref | `"x"` | VA of symbol x |
| PTE calculation | `pte3(x, root)` | Address of L3 PTE for x |
| Descriptor | `desc3(x)` | L3 descriptor value for x |
| Expression | `bvor(a, b)` | Bitwise OR |

### Register Normalization

- `X0-X30` → `R0-R30`
- `_PC` preserved as-is
- PSTATE fields merged into inline table

---

## Assertion Translation

### Basic Translation

```toml
# Input (Isla)
assertion = "0:X0 = 1"

# Output (ArchSem)
[[outcome]]
allowed = { regs = { "0" = { R0 = 0x1 } } }
```

### Logical Operators

**AND (`&`)** - Groups conditions in single outcome:
```toml
# Input
assertion = "0:X0 = 1 & 0:X1 = 2"

# Output
[[outcome]]
allowed = { regs = { "0" = { R0 = 0x1, R1 = 0x2 } } }
```

**OR (`|`)** - Creates separate outcome blocks:
```toml
# Input
assertion = "0:X0 = 1 | 0:X0 = 0"

# Output
[[outcome]]
allowed = { regs = { "0" = { R0 = 0x1 } } }

[[outcome]]
allowed = { regs = { "0" = { R0 = 0x0 } } }
```

### Inequality Operator

Supports both inline and wrapped forms:

```toml
# Input (inline)
assertion = "0:X4~2"

# Input (wrapped)
assertion = "~(0:X4=2)"

# Output
[[outcome]]
allowed = { regs = { "0" = { R4 = { op = "ne", val = 0x2 } } } }
```

### Memory Assertions

```toml
# Input
assertion = "*x = 1 & *y = 0"

# Output (with resolved addresses)
[[outcome]]
allowed = {
  mem = [
    { addr = 0x81000, value = 0x100000000000000, size = 8 },
    { addr = 0x82000, value = 0x0, size = 8 }
  ]
}
```

**Note**: Memory values are stored in little-endian format (value shifted left by 56 bits for 8-byte reads).

### Negation

```toml
# Input (negated assertion → forbidden)
assertion = "~(0:X0 = 1)"
expect = "sat"

# Output
[[outcome]]
forbidden = { regs = { "0" = { R0 = 0x1 } } }
```

### Multi-thread Assertions

```toml
# Input
assertion = "0:X0 = 1 & 1:X1 = 2"

# Output
[[outcome]]
allowed = {
  regs = {
    "0" = { R0 = 0x1 },
    "1" = { R1 = 0x2 }
  }
}
```

---

## Page Table Descriptors

### Code Pages (Executable, Read-Only)
- Descriptor: `0x6C3`
- Attributes:
  - `AP[2:1] = 0b11` (Read-only for EL1 and EL0)
  - `SH[1:0] = 0b11` (Inner shareable)
  - `AF = 1` (Access flag set)
  - `UXN = 0, PXN = 0` (Executable)

### Data Pages (Non-Executable, Read-Write)
- Descriptor: `0x60000000000743`
- Attributes:
  - `AP[2:1] = 0b01` (Read-write)
  - `SH[1:0] = 0b11` (Inner shareable)
  - `AF = 1` (Access flag set)
  - `UXN = 1, PXN = 1` (Non-executable)

### Identity Mappings

The converter automatically creates identity mappings for:
1. **Code regions** - Thread code and exception handlers (executable)
2. **Page tables** - All allocated page table pages (data)
3. **Data symbols** - Physical addresses used in tests (data)

This ensures hardware page table walks can access all necessary memory.

---

## Termination Conditions

### Standard Threads
```toml
# PC after last instruction
[[termCond]] # 0
_PC = 0x200c  # base (0x2000) + size (12)
```

### Threads with Exception Handlers

If a thread has an associated exception handler that doesn't end with `ERET`:
```toml
# PC at end of handler
[[termCond]] # 0
_PC = 0x1408  # handler end address
```

---

## Complete Example

### Input (Isla DSL)
```toml
arch = "AArch64"
name = "simple_test"
symbolic = ["x"]

page_table_setup = """
    physical pa1;
    x |-> pa1;
    *pa1 = 0x42;
"""

[thread.0]
init = { X1 = "x" }
code = "LDR X0,[X1]"

[final]
assertion = "0:X0 = 0x42"
```

### Output (ArchSem TOML)
```toml
arch = "AArch64"
name = "simple_test"
# Symbolic Variable Mapping:
# x = 0x4000000000 (mapped to PA pa1=0x81000)

[[memory]] # Initial Data
base = 0x81000
size = 8
data = 0x42

[[memory]] # L0 Table Pointer
base = 0x80100
size = 8
data = 0x82003

# ... (more PT entries)

[[memory]] # Code 0 (PA=0x2000)
base = 0x2000
size = 4
data = [0xf9400020]

[[registers]] # 0
_PC = 0x4000002000
R1 = 0x4000000000
SCTLR_EL1 = 0x1
TTBR0_EL1 = 0x80000
# ... (other registers)

[[termCond]] # 0
_PC = 0x4000002004

[[outcome]]
allowed = { regs = { "0" = { R0 = 0x42 } } }
```
