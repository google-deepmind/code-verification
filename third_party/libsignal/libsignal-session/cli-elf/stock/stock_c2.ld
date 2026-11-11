/* Deterministic stock `ld.lld` linker script v2 (C2 `D-C2f = 2C` variant) for `libsignal-cli`.
 *
 * Identical to `cli-elf/stock.ld` except that the 4 de-hooked `libc.a` string primitives
 * (`memmove.lo` -> `memcmp.lo` -> `bcmp.lo` -> `strlen.lo`) are placed at the tail of `.text.b_pre`
 * (`:text_b`, `< e_entry`) immediately after `memset.lo` instead of `.text.crate` (`:text_a`),
 * preserving `bcmp`'s `b memcmp` branch word and the 56-byte `memcmp + bcmp` hull.
 * Generated deterministically from `cli-elf/stock.ld` by `_render_c2_stock_ld`.
 *
 * Layout invariants (2-config `--no-relax` `StdBin` ELF with `rustc 1.98.1` `self-contained/libc.a`):
 *   1. Four page-aligned, non-overlapping W^X `PT_LOAD` segments (`:ro` R, `:text_a` RX, `:text_b` RX,
 *      `:data` RW) starting at `0x400000` with `FILEHDR PHDRS` mapped at `[0x400000, 0x400000 + SIZEOF_HEADERS)`
 *      for musl `AT_PHDR` / `AT_PHNUM` discovery (`e_phnum = 7`):
 *      - `:ro`     `FLAGS(4)` (`.rodata` plus optional `.rodata.lib2` for C2 `lib2_*.o` RO / `.data.rel.ro`);
 *      - `:text_a` `FLAGS(5)`: `.text.crate` holds all `lib0_*.o` crate blocks (including `main`),
 *        hooked `lib1_*.o` I/O definers (`write_file`, `write_stdout`), `extern_stubs_clean.o`
 *        (`udf #0` fail-stop/hook/panic stubs + displaced weak `__aarch64_*` atomics + in-place
 *        `KEEP(.text.__retired_*)` retired stub slots), and `.text.compiler_rt.*`;
 *      - `:text_b` `FLAGS(5)` (`StdBinaryLayout.rxProgram`):
 *        - `.text.b_pre` (`< e_entry`) holds non-hook `lib1_*.o` definers (`read_file`, `read_stdin`,
 *          `RawVecInner::finish_grow`), `rdl_shim.o` (`__rdl_*` + 5 `__rust_*` shims), and musl
 *          `memcpy.lo` / `memset.lo` followed by `memmove.lo` -> `memcmp.lo` -> `bcmp.lo` -> `strlen.lo`
 *          (`< e_entry`);
 *        - `.text` begins at `0x1000`-aligned `e_entry` with `KEEP(*crt1.o(.text.start ...))`
 *          (`_start == e_entry`), followed by `.init`, musl startup/exit/libc + `mallocng` + `main_rust.o`
 *          text, and `.fini`, followed at the `:text_b` tail by optional `.text.lib2` (`*lib2_*.o`,
 *          de-hooked `cli/rt` code enabled atomically at C2). Every hooked `libsignalSessionExterns`
 *          entry resolves `< e_entry` (`hstubLt`), `e_entry - base(main) > 0` (`hmainOff`), and
 *          `0` `externAt?` hook keys lie in `[e_entry, text_b_end)` (`lib2` is de-hooked code).
 *   2. Page-aligned RW layout in `:data`:
 *      - `.tdata`, `.tbss` (`PT_TLS` `0/0`), and `.data.crate` occupy the initial `:data` page;
 *      - Top-level `PROVIDE_HIDDEN` (`indent == 0` in `link.map`) and `. = ALIGN(0x1000);` align
 *        `.init_array`, `.fini_array`, `.data`, `.got`, and `.bss.musl` to the next `0x1000` boundary;
 *      - Crate `.bss` follows disjointly after `.bss.musl`.
 */
ENTRY(_start)

PHDRS
{
  phdr   PT_PHDR PHDRS;
  ro     PT_LOAD FILEHDR PHDRS FLAGS(4);
  text_a PT_LOAD FLAGS(5);
  text_b PT_LOAD FLAGS(5);
  data   PT_LOAD FLAGS(6);
  tls    PT_TLS;
  stack  PT_GNU_STACK FLAGS(6);
}

SECTIONS
{
  PROVIDE_HIDDEN(_DYNAMIC = 0);
  . = 0x400000 + SIZEOF_HEADERS;

  .rodata : {
    *(EXCLUDE_FILE(*lib2_*.o) .rodata EXCLUDE_FILE(*lib2_*.o) .rodata.* EXCLUDE_FILE(*lib2_*.o) .gnu.linkonce.r.*)
    *(EXCLUDE_FILE(*lib2_*.o) .data.rel.ro EXCLUDE_FILE(*lib2_*.o) .data.rel.ro.*)
  } :ro =0

  /* `.data.rel.ro` precedes `.rodata` in `.rodata.lib2` so `lib2_5.o` (`SystemTime::add`, whose
   * only RO input is a 45-byte `align=1` `.rodata..Lanon` panic string) sits strictly at the end
   * of `.rodata.lib2`: dropping `time_add` truncates `.rodata.lib2` without shifting earlier
   * `.data.rel.ro` `Location` records or `.rodata` tables. */
  .rodata.lib2 : {
    *lib2_*.o(.data.rel.ro .data.rel.ro.*)
    *lib2_*.o(.rodata .rodata.* .gnu.linkonce.r.*)
  } :ro =0

  . = ALIGN(0x1000);

  .text.crate : ALIGN(0x1000) {
    *lib0_*.o(.text .text.*)
    *lib1_*.o(.text.*10write_file .text.*12write_stdout)
    main.o(.text .text.*)
    */main.o(.text .text.*)
    *extern_stubs_clean.o(.text .text.*)
    KEEP(*extern_stubs_clean.o(.text.__retired_*))
    *(EXCLUDE_FILE(*lib2_*.o) .text.compiler_rt.*)
  } :text_a =0

  . = ALIGN(0x1000);

  .text.b_pre : ALIGN(0x1000) {
    *lib1_*.o(.text .text.*)
    *rdl_shim.o(.text .text.*)
    memcpy.o(.text .text.*)
    */memcpy.o(.text .text.*)
    *libc.a:memcpy.lo(.text .text.*)
    *memcpy.lo(.text .text.*)
    memset.o(.text .text.*)
    */memset.o(.text .text.*)
    *libc.a:memset.lo(.text .text.*)
    *memset.lo(.text .text.*)
    memmove.o(.text .text.*)
    */memmove.o(.text .text.*)
    *libc.a:memmove.lo(.text .text.*)
    *memmove.lo(.text .text.*)
    memcmp.o(.text .text.*)
    */memcmp.o(.text .text.*)
    *libc.a:memcmp.lo(.text .text.*)
    *memcmp.lo(.text .text.*)
    bcmp.o(.text .text.*)
    */bcmp.o(.text .text.*)
    *libc.a:bcmp.lo(.text .text.*)
    *bcmp.lo(.text .text.*)
    strlen.o(.text .text.*)
    */strlen.o(.text .text.*)
    *libc.a:strlen.lo(.text .text.*)
    *strlen.lo(.text .text.*)
    *(EXCLUDE_FILE(*lib2_*.o) .text.strlen)
  } :text_b =0

  . = ALIGN(0x1000);

  .text : ALIGN(0x1000) {
    KEEP(*crt1.o(.text.start .text .text.*))
    KEEP(*(SORT_NONE(.init)))
    *(EXCLUDE_FILE(*lib2_*.o) .text EXCLUDE_FILE(*lib2_*.o) .text.* EXCLUDE_FILE(*lib2_*.o) .gnu.linkonce.t.*)
    KEEP(*(SORT_NONE(.fini)))
  } :text_b =0

  .text.lib2 : {
    *lib2_*.o(.text .text.*)
  } :text_b =0

  . = ALIGN(0x1000);

  .tdata : {
    *(.tdata .tdata.* .gnu.linkonce.td.*)
  } :data :tls

  .tbss : {
    *(.tbss .tbss.* .gnu.linkonce.tb.*)
  } :data :tls

  .data.crate : {
    *lib0_*.o(.data .data.*)
    main.o(.data .data.*)
    */main.o(.data .data.*)
    *extern_stubs_clean.o(.data .data.*)
    memcpy.o(.data .data.*)
    */memcpy.o(.data .data.*)
    *libc.a:memcpy.lo(.data .data.*)
    memset.o(.data .data.*)
    */memset.o(.data .data.*)
    *libc.a:memset.lo(.data .data.*)
    memmove.o(.data .data.*)
    */memmove.o(.data .data.*)
    *libc.a:memmove.lo(.data .data.*)
    memcmp.o(.data .data.*)
    */memcmp.o(.data .data.*)
    *libc.a:memcmp.lo(.data .data.*)
    bcmp.o(.data .data.*)
    */bcmp.o(.data .data.*)
    *libc.a:bcmp.lo(.data .data.*)
  } :data

  . = ALIGN(0x1000);

  PROVIDE_HIDDEN(__init_array_start = .);
  .init_array : ALIGN(0x1000) {
    KEEP(*(SORT_BY_INIT_PRIORITY(.init_array.*) SORT_BY_INIT_PRIORITY(.ctors.*)))
    KEEP(*(.init_array .ctors))
  } :data
  PROVIDE_HIDDEN(__init_array_end = .);

  . = ALIGN(8);
  PROVIDE_HIDDEN(__fini_array_start = .);
  .fini_array : ALIGN(8) {
    KEEP(*(SORT_BY_INIT_PRIORITY(.fini_array.*) SORT_BY_INIT_PRIORITY(.dtors.*)))
    KEEP(*(.fini_array .dtors))
  } :data
  PROVIDE_HIDDEN(__fini_array_end = .);

  .data : {
    *(.data .data.* .gnu.linkonce.d.*)
  } :data

  .got : {
    *(.got .got.*)
  } :data

  .bss.musl : {
    *(EXCLUDE_FILE(*lib0_*.o main.o */main.o *extern_stubs_clean.o memcpy.o */memcpy.o memset.o */memset.o memmove.o */memmove.o memcmp.o */memcmp.o bcmp.o */bcmp.o) .bss)
    *(EXCLUDE_FILE(*lib0_*.o main.o */main.o *extern_stubs_clean.o memcpy.o */memcpy.o memset.o */memset.o memmove.o */memmove.o memcmp.o */memcmp.o bcmp.o */bcmp.o) .bss.*)
    *(EXCLUDE_FILE(*lib0_*.o main.o */main.o *extern_stubs_clean.o memcpy.o */memcpy.o memset.o */memset.o memmove.o */memmove.o memcmp.o */memcmp.o bcmp.o */bcmp.o) COMMON)
  } :data

  .bss : {
    *(.bss .bss.* .gnu.linkonce.b.* COMMON)
  } :data

  .stock.stub_manifest 0 (INFO) : {
    KEEP(*(.stock.stub_manifest))
  }

  .symtab 0 : { *(.symtab) }
  .strtab 0 : { *(.strtab) }
  .shstrtab 0 : { *(.shstrtab) }

  /DISCARD/ : {
    *(.eh_frame*)
    *(.gcc_except_table*)
    *(.comment)
    *(.note*)
    *(.llvm_addrsig)
  }
}
