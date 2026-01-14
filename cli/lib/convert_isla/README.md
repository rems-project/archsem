# Convert Isla

Converts Isla DSL TOML files to ArchSem TOML format for AArch64 litmus test execution.

## Documentation

- **[ISLA_FORMAT.md](./ISLA_FORMAT.md)** — Isla DSL TOML format specification (input)
- **[TOML_SPEC.md](./TOML_SPEC.md)** — ArchSem TOML format specification (output)
- **[TRANSLATION.md](./TRANSLATION.md)** — Isla DSL → ArchSem translation rules

## Architecture

The converter is organized into focused modules:

- **`input_parser.ml`** — Parse Isla TOML files
  - Thread definitions (`[thread.N]`)
  - Exception handler sections (`[section.name]`)
  - Page table setup DSL
  - Supports both `reset` and `init` register sections

- **`page_tables.ml`** — Page table installation and memory management
  - DSL statement processing
  - Identity mapping installation
  - Descriptor generation (code/data)
  - Multi-level page table construction

- **`output_emitter.ml`** — ArchSem TOML generation
  - Memory region emission (code, data, page tables)
  - Register initialization
  - Termination conditions
  - Outcome assertions (with inequality support)

- **`converter.ml`** — Main orchestration logic
  - Coordinates parsing, translation, and output
  - Handles both usermode and page table tests

Supporting modules:
- **`ast.ml`** — Abstract syntax tree for DSL
- **`lexer.mll`** — Lexical analyzer for DSL
- **`parser.mly`** — Parser for page table DSL
- **`symbols.ml`** — Symbol table for VA/PA/IPA management
- **`allocator.ml`** — Physical address allocator
- **`assembler.ml`** — AArch64 instruction encoder
- **`evaluator.ml`** — Expression evaluator for register init

## Usage

### Convert a single test

```bash
dune exec -- cli/bin/convert_isla.exe input.toml -o output_dir/
```

### Convert with usermode mode (no page tables)

```bash
dune exec -- cli/bin/convert_isla.exe input.toml --usermode -o output_dir/
```

### Run batch conversion and testing

```bash
./run_litmus_tests.sh [pattern] [timeout]
```

Example:
```bash
# Run all tests in exn/HAND directory with 180s timeout
./run_litmus_tests.sh "exn/HAND/*.litmus.toml" 180

# Run all tests with default 180s timeout
./run_litmus_tests.sh
```

## Test Results

The converter integrates with the litmus test runner which produces:

- **EQUAL** — Test results match expected outcomes
- **DIFFERENT** — Test results differ from expected outcomes (coverage fail)
- **ERROR** — Model failed during execution (unsupported instruction, etc.)

## Logging

The test runner creates detailed logs:

- `test_results.log` — Complete timestamped results
- `test_equal.log` — Tests with EQUAL results
- `test_different.log` — Tests with DIFFERENT results and reasons
- `test_error.log` — Tests with ERROR or CRASH results
- `test_timeout.log` — Tests that timed out
- `test_convert_error.log` — Tests that failed during conversion
- `test_fails.log` — Detailed error information for failures

## Features

### Page Table Support

- Multi-level page table generation (L0-L3)
- Identity mappings for code and data
- Custom table definitions (`s1table`, `s2table`)
- Descriptor attribute control (AP, SH, UXN, PXN)
- Break-Before-Make variant mappings (`?->`)

### Register Initialization

Supports symbolic expressions in register init:
```toml
[thread.0.init]
X1 = "x"                    # Symbolic variable
X2 = "pte3(x, page_table_base)"  # Calculate PTE address
X3 = "0x1000"              # Literal value
```

Both `[thread.N.reset]` (page table tests) and `[thread.N.init]` (usermode tests) formats are supported.

### Assertion Translation

Converts Isla assertions to ArchSem outcomes:
```toml
# Isla format
assertion = "0:X0=1 & 0:X1=2 | 0:X0=0"

# ArchSem format
[[outcome]]
allowed = { regs = { "0" = { R0 = 1, R1 = 2 } } }

[[outcome]]
allowed = { regs = { "0" = { R0 = 0 } } }
```

Supports both equality (`=`) and inequality (`~`) operators:
```toml
# Inequality: thread 0 register X4 should NOT equal 2
assertion = "~(0:X4=2)"
# or
assertion = "0:X4~2"

# Output
allowed = { regs = { "0" = { R4 = { op = "ne", val = 2 } } } }
```

### Memory Assertions

Supports memory location checks:
```toml
# Check symbolic variable value
assertion = "*x=1 & *y=0"

# Output includes physical address resolution
allowed = { mem = [
  { addr = 0x81000, value = 0x100000000000000, size = 8 },
  { addr = 0x82000, value = 0x0, size = 8 }
] }
```

## Development

Build the project:
```bash
dune build
```

Run tests:
```bash
dune runtest
```

Clean build artifacts:
```bash
dune clean
```
