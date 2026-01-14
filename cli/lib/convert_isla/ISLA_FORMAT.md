# Isla System Litmus Test TOML Format

## 1. Top-Level Structure

The file follows the standard TOML format. The root object contains metadata and configuration strings.

| Key | Type | Description |
| :--- | :--- | :--- |
| `arch` | String | Target architecture, e.g., `"AArch64"`. |
| `name` | String | Unique identifier for the test case. |
| `symbolic` | List\<String\> | List of symbolic address variables (e.g., `["x", "y"]`). |
| `page_table_setup` | String | Embedded DSL script defining physical memory layout and page tables. |
| `[thread.N]` | Table | Defines code and meta-info for thread `N` (0-indexed). |
| `[thread.N.reset]` | Table | Defines initial register values for thread `N` using an expression DSL. |
| `[section.<name>]` | Table | Defines exception handler code sections. |
| `[final]` | Table | Defines the post-condition assertion. |

---

## 2. Page Table Setup DSL (`page_table_setup`)

This section uses a domain-specific language to define variables for physical addresses (PA), intermediate physical addresses (IPA), and their mappings.

### Grammar by Example

```
page_table_setup = """
    # Options
    option default_tables = false;

    # Declarations
    physical pa1 pa2;
    intermediate ipa1;
    virtual x y;
    aligned 2097152 virtual z; # Aligned virtual address

    # Table definitions
    s1table host_s1 0x2C0000 {
        x |-> ipa1;
    }
    s2table vm_stage2 0x260000 {
        ipa1 |-> pa1 with [AP = 0b00] at level 3;
        ipa1 ?-> invalid at level 2;
        ipa1 ?-> pa2 with default at level 2;
    }

    # Mappings
    x |-> pa1;                 # Normal mapping
    x ?-> pa1;                 # Variant mapping (alternative)
    x |-> invalid;             # Invalid mapping
    x |-> table(pa2);          # Map to table at pa2
    x |-> raw(2);              # Map to raw descriptor value 2

    # Attributes
    x |-> pa1 with [AP=0b11, SH=0b10];

    # Identity Mapping
    identity 0x1000 with code;

    # Memory Initialization
    *pa1 = 0x1234;
"""
```

### Keyword Reference

*   `physical`: Declare physical address symbols.
*   `intermediate`: Declare intermediate physical address symbols (IPA).
*   `virtual`: Declare virtual address symbols.
*   `aligned N virtual X`: Declare virtual symbol X aligned to N.
*   `s1table`, `s2table`: Define specific stage 1 or stage 2 tables.
*   `|->`: Create a mapping.
*   `?->`: Create a variant mapping (used for testing translation lookups).
*   `invalid`: Map to an invalid descriptor.
*   `table(ADDR)`: Map to a next-level table at ADDR.
*   `raw(VAL)`: Map to a raw integer descriptor.
*   `identity ADDR with code`: Identity map a code page.
*   `option KEY = VAL`: Configuration options.
*   `with [ATTR = VAL]`: Set descriptor attributes (AP, SH, etc).
*   `with default`: Use default attributes.

### Grammar Specification

```ebnf
setup_block   ::= statement*
statement     ::= declaration ";"
                | mapping ";"
                | memory_init ";"
                | identity_map ";"
                | table_def ";"
                | option_def ";"

(* Variable Declarations *)
declaration   ::= "physical" name_list
                | "intermediate" name_list
                | "virtual" name_list
                | "aligned" integer "virtual" identifier

(* Configuration *)
option_def    ::= "option" identifier "=" value

(* Page Table Mappings *)
mapping       ::= va_expr "|->" target_expr attributes_opt level_opt
                | va_expr "?->" target_expr attributes_opt level_opt

target_expr   ::= pa_expr
                | "invalid"
                | "table" "(" pa_expr ")"
                | "raw" "(" value ")"

attributes_opt ::= "with" "[" attr_list "]"
                 | "with" "default"
                 | (* empty *)

attr_list     ::= identifier "=" value ("," attr_list)?

level_opt     ::= "at level" integer
                | (* empty = default leaf level *)

(* Table Definition Block *)
table_def     ::= ("s1table" | "s2table") identifier address "{" mapping* "}"

(* Initial Memory Values *)
memory_init   ::= "*" pa_expr "=" value

(* Identity Mapping for Code *)
identity_map  ::= "identity" address "with" "code"

(* Primitives *)
va_expr       ::= identifier  (* Virtual Address symbolic name *)
pa_expr       ::= identifier  (* Physical/Intermediate Address symbolic name or literal *)
value         ::= integer | "true" | "false"
address       ::= hex_literal
```

### Semantics

- **Declarations**: `physical pa1` creates a physical address variable `pa1`.
- **Mappings (`|->`)**:
  - `x |-> pa1` installs a page table entry (PTE) mapping virtual address `x` to physical address `pa1`.
  - `x |-> invalid` installs an invalid PTE for `x`.
  - `x |-> table(pa_table) at level 2` creates a table descriptor at level 2 pointing to a next-level table at `pa_table`.
- **Variant Mappings (`?->`)**:
  - Used in Break-Before-Make (BBM) tests where the TLB might hold multiple entries or the memory system is in a transitional state.
  - `x ?-> pa2` implies that a mapping to `pa2` is *also* potentially valid via strict aliasing validation.
- **Explicit Levels**: `at level N` specifies at which translation level (0-3 for AArch64) the entry should be placed.
- **Custom Tables**:
  ```
  s1table new_table 0x280000 {
      x |-> invalid;
  }
  ```
  Defines a new Stage 1 translation table at physical address `0x280000` named `new_table`.

---

## 3. Register Initialization (`[thread.N.reset]` or `[thread.N.init]`)

The converter supports both `reset` (page table tests) and `init` (usermode tests) sections. Both can be specified as:
- Separate table: `[thread.N.reset]` or `[thread.N.init]`
- Inline table: `init = { X1 = "x", X2 = "y" }`

The values in the reset/init table are strings evaluated at test generation/initialization time to determine 64-bit register values.

### Grammar

```ebnf
expr          ::= function_call
                | literal
                | reference
                | label_ref

function_call ::= "extz" "(" value "," width ")"        (* Zero extend *)
                | "pte" level "(" va_ref "," table_ref ")"  (* Calculate PTE address *)
                | "mkdesc" level "(" desc_args ")"      (* Create descriptor *)
                | "page" "(" va_ref ")"                 (* Get page number/aligned addr *)

level         ::= "0" | "1" | "2" | "3"

desc_args     ::= "oa" "=" pa_ref
                | "table" "=" pa_ref

ttbr_args     ::= "asid" "=" value "," "base" "=" table_ref
                | "base" "=" table_ref

literal       ::= "0x" hex_digits
                | "0b" binary_digits
                | digits

reference     ::= identifier          (* symbolic var like 'x' or table name *)
table_ref     ::= identifier          (* page_table_base, s2_page_table_base, or custom table name *)
label_ref     ::= identifier ":"      (* code label like 'L0:' *)
```

### Functions & Semantics

| Function | Argument Example | Description |
| :--- | :--- | :--- |
| `extz(val, method)` | `extz(0x1000, 64)` | Zero-extends `val` to `bits`. |
| `pteN(va, base)` | `pte3(x, page_table_base)` | Computes the physical address of the Level `N` Page Table Entry for virtual address `va`, relative to `base`. Valid levels are 0, 1, 2, 3. |
| `mkdescN(...)` | `mkdesc3(oa=pa1)` | Constructs a raw 64-bit descriptor for Level `N`. <br> - Use `mkdesc3(oa=pa)` for leaf page descriptors.<br> - Use `mkdesc2(table=pa)` for table descriptors pointing to next level. |
| `page(va)` | `page(x)` | Returns the page-aligned address (or PFN) for variable `va` (masks lower 12 bits). |
| `ttbr` | `ttbr(asid=0x0, base=table)` | Constructs a TTBR register value with the given ASID/VMID and base address. |
| `bvlshr(val, shift)` | `bvlshr(ipa1, 12)` | Logical shift right of `val` by `shift` bits. |
| `bvor(val1, val2)` | `bvor(...)` | Bitwise logical OR of two values. |
| `tableN(val)` | `table3(walkx)` | Interpretation of `val` as a level `N` table descriptor/address (context-dependent). |
| `offset(...)` | `offset(va=x, level=3)` | Calculates the offset (index * 8) for the given VA at the specified level. |

### Special Identifiers
- `page_table_base`: Implicit verification variable pointing to the root of the default page tables.
- `s2_page_table_base`: Implicit variable for Stage 2 translation tables (virtualization).
- **Table References**: You can refer to named tables (e.g., `new_table` from the scalar setup) in `pte` functions.

---

## 4. Exception Handlers (`[section.<name>]`)

Defines code blocks that serve as exception vectors or specific handler routines.

- **Key `address`**: Sets the physical placement of this code block (e.g., `0x1400`).
- **Key `code`**: The assembly instructions for the handler.

Example:
```toml
[section.thread0_el2_handler_lower_exc]
address = "0x2400"
code = """
    MOV X2,#0
    ERET
"""
```

---

## 5. Metadata & Assertions

- **Thread Code**:
  - `init`: Table for initial system register overrides (often empty).
  - `code`: The main assembly loop for the thread.

- **Final Assertion**:
  - `expect` (Optional): String indicating expected result, e.g., `"sat"` or `"unsat"`.
  - `assertion`: Boolean expression checking the final state.
    - **Operands**:
      - `Thread:Register`: e.g., `1:X0` (Thread 1, Register X0).
      - `*Address`: e.g., `*pa1` (Value at physical address `pa1`).
    - **Operators**:
      - `&`: Logical AND
      - `|`: Logical OR
      - `=`: Equality
      - `~`: Inequality (can be used inline or wrapping: `0:X4~2` or `~(0:X4=2)`)

## 6. Full Example (Multi-level)

```toml
arch = "AArch64"
name = "MultiLevel_Example"
symbolic = ["x"]

page_table_setup = """
    physical pa1;
    intermediate ipa1;

    # Implicit setup mapping x -> ipa1
    x |-> ipa1;

    # Custom Table Definition
    s1table custom_l3 0x300000 {
        x |-> pa1;
    };

    # Pointing Level 2 entry to the custom table manually
    x ?-> table(0x300000) at level 2;

    identity 0x1000 with code;
"""

[thread.0]
code = """
    LDR X0, [X1]
"""

[thread.0.reset]
R1 = "x"
R2 = "pte2(x, page_table_base)"          # L2 Entry Address
R3 = "mkdesc2(table=extz(0x300000, 64))" # L2 Table Descriptor

[final]
expect = "sat"
assertion = "0:X0 = 1 & *pa1 = 1"
```

## 7. Usermode Test Example (Inline Init)

```toml
arch = "AArch64"
name = "simple_load"
symbolic = ["x", "y"]

[thread.0]
init = { X1 = "x", X3 = "y" }  # Inline init format
code = """
    LDR W0,[X1]
"""

[final]
expect = "sat"
assertion = "0:X0~0"  # X0 should NOT equal 0
```
