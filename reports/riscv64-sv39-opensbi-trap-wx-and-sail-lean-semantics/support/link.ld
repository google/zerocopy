/*
 * Bare-metal RV64IM_Zicsr_Zifencei Sv39 high-half linker script for
 * QEMU `virt` + OpenSBI (`fw_dynamic`).
 *
 * Key invariants verified against qemu/qemu@08c9bbb825148dec9669f5184ecf18823bb6d631
 * (`hw/riscv/boot.c:286-293`):
 *   1. QEMU passes `boot_info.image_low_addr` (the lowest PT_LOAD `p_paddr`),
 *      NOT `e_entry`, to OpenSBI `fw_dynamic` as `next_addr`. Therefore
 *      `.text.boot` (`_start`) MUST be placed first at LMA `0x8020_0000`.
 *   2. Every section shares `VMA = LMA + KERNEL_VIRT_OFF` (`0xffff_ffc0_0000_0000`)
 *      so PC-relative `la` (`R_RISCV_PCREL_HI20`, `-C code-model=medium`) fits
 *      within +/-2 GiB and automatically resolves to physical addresses before
 *      `jr` to the high half and virtual addresses after.
 *   3. User payload section is named `.user_text` (not `.text.user`) so
 *      `*(.text .text.*)` in `.text` cannot swallow user code onto a kernel page.
 */
OUTPUT_ARCH(riscv)
ENTRY(_start)

KERNEL_PHYS_BASE = 0x80200000;
KERNEL_VIRT_OFF  = 0xffffffc000000000;
KERNEL_VIRT_BASE = KERNEL_PHYS_BASE + KERNEL_VIRT_OFF;

PHDRS
{
    boot   PT_LOAD FLAGS(5); /* R | X */
    text   PT_LOAD FLAGS(5); /* R | X */
    rodata PT_LOAD FLAGS(4); /* R */
    user   PT_LOAD FLAGS(5); /* R | X */
    data   PT_LOAD FLAGS(6); /* R | W */
}

SECTIONS
{
    . = KERNEL_VIRT_BASE;

    .text.boot : AT(ADDR(.text.boot) - KERNEL_VIRT_OFF) {
        KEEP(*(.text.boot))
        . = ALIGN(4096);
    } :boot

    .text : AT(ADDR(.text) - KERNEL_VIRT_OFF) {
        _text_start = .;
        *(.text .text.*)
        . = ALIGN(4096);
        _text_end = .;
    } :text

    .rodata : AT(ADDR(.rodata) - KERNEL_VIRT_OFF) {
        _rodata_start = .;
        *(.rodata .rodata.*)
        . = ALIGN(4096);
        _rodata_end = .;
    } :rodata

    .user_text : AT(ADDR(.user_text) - KERNEL_VIRT_OFF) {
        _user_code_start = .;
        KEEP(*(.user_text))
        . = ALIGN(4096);
        _user_code_end = .;
    } :user

    .data : AT(ADDR(.data) - KERNEL_VIRT_OFF) {
        _data_start = .;
        *(.data .data.*)
        . = ALIGN(4096);
    } :data

    .bss : AT(ADDR(.bss) - KERNEL_VIRT_OFF) {
        _bss_start = .;
        *(.bss .bss.* COMMON)
        . = ALIGN(4096);
        _bss_end = .;
    } :data

    /DISCARD/ : { *(.comment) *(.eh_frame*) *(.riscv.attributes) }
}
