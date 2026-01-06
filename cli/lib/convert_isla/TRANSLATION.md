# Isla DSL → ArchSem TOML Translation

## Overview

The `convert_litmus` tool transforms symbolic Isla TOML files into concrete ArchSem TOML files.

## Translation Summary

| Isla DSL | ArchSem TOML |
|----------|--------------|
| `arch = "AArch64"` | `arch = "Arm"` |
| `[thread.0] code = "..."` | `[[memory]] data=[opcodes]` |
| `[thread.0.reset] R0 = ...` | `[[registers]] R0 = 0x...` |
| `page_table_setup` | `[[memory]]` entries (PT) |
| `[final] assertion = ...` | `[[outcome]]` |
| *(implicit)* | `[[termCond]] _PC = <end>` |

---

## Address Allocation

### Virtual Addresses
- Start: `0x40_0000_0000`
- Auto-allocated for symbolic names

### Physical Addresses
- Start after page table root (~`0x81000`)
- Page tables occupy lower PA space

### Symbolic Mapping Header
Debug comments in output:

```toml
# Symbolic Variable Mapping:
# trap = 0x4000000000 (mapped to PA pa1=0x81000)
# done = 0x4000001000 (mapped to PA pa2=0x82000)
```

---

## Page Table DSL

### Syntax

```
va_name |-> pa_name           # Map VA to PA
identity 0x1000 with code;    # Identity mapping (VA=PA)
```

### Output
Generates `[[memory]]` blocks with 64-bit PT entries:

```toml
[[memory]]
base = 0xd3000
size = 8
data = 0x403
```

---

## Code Translation

Assembly strings → encoded opcodes:

```
Input:  code = "str x0, [x1]\ndmb sy"
Output: data = [0xf9000020, 0xd5033fbf]
```

- Size = number of instructions × 4
- `_PC` in registers = code base address
- `_PC` in termCond = base + size

---

## Assertion Translation

### Isla Format
```toml
[final]
assertion = "X0 == 1 & X1 == 0 | X0 == 0"
```

### ArchSem Format
- `&` → grouped in single outcome
- `|` → separate `[[outcome]]` blocks
- `Xn` → `Rn`
- `==` → `{ op = "eq", val = ... }`
- `!=` → `{ op = "ne", val = ... }`

```toml
[[outcome]]
allowed.0 = { R0 = { op = "eq", val = 0x1 }, R1 = { op = "eq", val = 0x0 } }

[[outcome]]
allowed.0 = { R0 = { op = "eq", val = 0x0 } }
```
