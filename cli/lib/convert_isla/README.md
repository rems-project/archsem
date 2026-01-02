# ArchSem TOML Format Specification & Translation

## Overview

The transformation pipeline converts symbolic, DSL-heavy Isla TOML files into concrete, literal ArchSem TOML files.

| Feature | Input (Isla TOML) Reference | Output (ArchSem TOML) |
| :--- | :--- | :--- |
| **Architecture** | `arch = "AArch64"` | `arch = "Arm"` |
| **Test Name** | `name = "Test"` | `name = "Test"` |
| **Symbolic Header** | N/A | `# Name = 0xVA (mapped to PA Name=0xPA)` |
| **Code** | `[thread.0] code = "..."` | `[[memory]] base=..., size=4, data=[hex...]` |
| **Page Tables** | `page_table_setup` | `[[memory]] base=..., size=8, data=0x...` |
| **Registers** | `[thread.0.reset] R0 = ...` | `[[registers]] R0 = 0x...` |
| **Termination** | Implicit | `[[termCond]] _PC = <end_addr>` |
| **Expectations** | `[final] assertion = ...` | `[[expected]] [expected.TID] R0=1` |

## Output Organization

The output file is structured in a strict order to ensure readability and determinism:

1.  **Metadata**: `arch`, `name`.
2.  **Symbolic Mapping**: Comments listing VA->PA mappings.
3.  **Memory - Initial Data**: `MemInit` blocks from the DSL.
4.  **Memory - Page Tables**: Generated Page Table mappings.
5.  **Memory - Code**: Executable code regions for each thread.
6.  **Registers**: Initial register state per thread.
7.  **Termination**: End conditions (`_PC`).
8.  **Expectations**: Final assertion values.

## Concrete Structure details

### 1. Symbolic Variable Mapping (Header)

The header provides debug information mapping symbolic names from the source DSL to their allocated Virtual Addresses (VA) and, if applicable, the mapped Physical Address (PA).

```toml
# Symbolic Variable Mapping:
# trap = 0x4000000000 (mapped to PA pa1=0x81000)
# done = 0x4000001000 (mapped to PA pa2=0x82000)
```

### 2. Memory Sections (`[[memory]]`)

All memory regions are defined in `[[memory]]` blocks. The format differs slightly between Data/PT entries and Code.

#### Initial Data & Page Tables
Used for memory initializations and page table entries.
*   **Size**: Always `8` (bytes).
*   **Data**: A **single 64-bit value**.

```toml
[[memory]] # Initial Data
base = 0x81000
size = 8
data = 0x0

[[memory]] # Level 3 Entry for VA 0x4000000000
base = 0xd3000
size = 8
data = 0x403
```

#### Code Regions
Used for the executable instructions of each thread.
*   **Size**: Always `4` (representing instruction size/stride).
*   **Data**: An **array** of 32-bit instruction opcodes.

```toml
[[memory]] # Code 0 (PA=0x60000)
base = 0x60000
size = 4
data = [0xf9000020, 0xd5033bbf, ...]
```

### 3. Registers (`[[registers]]`)

Each `[[registers]]` block initializes the state for a specific thread. Blocks are sorted by Thread ID (`thread.0`, `thread.1`, ...).

*   `_PC`: Calculated start address (Virtual Address) of the code.
*   **Defaults**: Registers not explicitly reset are initialized to `0x0`.

```toml
[[registers]] # 0
_PC = 0x60000
R0 = 0x1
PSTATE.EL = 0x1
```

### 4. Page Table Generation DSL

The `convert_litmus` tool interprets the `page_table_setup` block to generate the `[[memory]]` entries.

*   **Syntax**: `va_name |-> pa_name`
*   **Identity Mapping**: `identity 0x1000 with code;` (Forces VA=PA for code, maps PA 1:1).
*   **Automatic Allocation**:
    *   **VAs**: Starts at `0x40_0000_0000`.
    *   **PAs**: Starts after the Page Table root (typically around `0x81000` depending on table size).

### 5. Termination Conditions (`[[termCond]]`)

Defines where execution should stop for each thread.
*   `_PC`: Code Start Address + (Number of Instructions * 4).

```toml
[[termCond]] # 0
_PC = 0x60028
```

### 6. Expected States (`[[expected]]`)

Translates the `[final]` assertions.
*   **Alternatives**: Constraints separated by `|` generate multiple `[[expected]]` blocks (not currently standard in all ArchSem runners, but supported by format).
*   **Grouping**: Constraints separated by `&` are grouped into a single expectation.
*   **Register Mapping**: `Xn` registers in assertions are mapped to `Rn`.

```toml
[[expected]]
[expected.0]
R0 = 0x1
```
