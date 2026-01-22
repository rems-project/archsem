# ArchSem TOML Specification

## Overview

This document specifies the concrete ArchSem TOML format used for litmus test definitions.

## File Structure

```toml
arch = "Arm"
name = "TestName"

[config]
FEAT_ETS2 = true

[[registers]]   # Per-thread register init
[[memory]]      # Memory regions (code + data)
[[termCond]]    # Termination conditions
[[outcome]]     # Possible outcomes
```

---

## 1. Metadata

```toml
arch = "Arm"
name = "MP+dmbs"
```

## 2. Configuration (`[config]`)

Optional system-level feature flags.

```toml
[config]
FEAT_ETS2 = true
```

---

## 3. Registers (`[[registers]]`)

One block per thread, ordered by Thread ID (0, 1, ...).

| Field | Description |
|-------|-------------|
| `_PC` | Program Counter (start address) |
| `Rn` | General-purpose registers |
| `PSTATE` | Processor state (inline table) |
| `SCTLR_EL1` | System control register |

```toml
[[registers]]
_PC = 0x500
R0 = 0x1000
R1 = 0x100
SCTLR_EL1 = 0x0
PSTATE = { "EL" = 0b00, "SP" = 0b0 }
```

---

## 4. Memory (`[[memory]]`)

### Code Regions

Executable instructions for a thread.

| Field | Value |
|-------|-------|
| `base` | Start address |
| `size` | Total bytes (num_instructions × 4) |
| `data` | Array of 32-bit opcodes |

```toml
[[memory]]
base = 0x500
size = 12
data = [0xf8206822, 0xd5033fbf, 0xf8236885]
```

### Data Regions

Shared memory locations.

| Field | Value |
|-------|-------|
| `base` | Address |
| `size` | Bytes (typically 8) |
| `data` | Single value |

```toml
[[memory]]
base = 0x1100
size = 8
data = 0
```

---

## 5. Termination Conditions (`[[termCond]]`)

One block per thread, specifying the end address.

```toml
[[termCond]]
_PC = 0x50C   # Thread 0: base + size
```

---

## 6. Outcomes (`[[outcome]]`)

Defines expected final states. Each outcome is a separate block.

### Syntax

```toml
[[outcome]]
allowed = { regs = { "<TID>" = { <REG> = <VALUE> } } }
# or with operator
allowed = { regs = { "<TID>" = { <REG> = { op = "eq"|"ne", val = <VALUE> } } } }
# with memory
observable = { mem = [{ addr = <ADDR>, value = <VALUE>, size = 8 }] }
# combined
observable = { regs = {...}, mem = [...] }
```

- `observable`: Defines outcomes that could be observable (coverage check).
- `unobservable`: Defines outcomes that should NOT be reachable (safety check).
