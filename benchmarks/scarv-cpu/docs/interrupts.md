
## Interrupt Handling.

*Describes how the SCARV-CPU handles and routes interrupts.*

---

## Interrupt Support:

The SCARV-CPU supports four classes of interrupts.

- Machine Timer Interupts, as described in the RISC-V privilieged
  Architecture specification (PRA).

- Machine Software Interupts, as described in the RISC-V PRA.

- Machine External Interrupts, as described in the RISC-V PRA.

- Non-maskable Interrupts (NMIs), which act like external interrupts,
  but cannot be selectivley disabled.

- Vectored interrupts are supported.

  - When in direct interrupt mode (`mtvec.mode=0`), the `mtvec.base`
    handler address must be 4-byte aligned.

  - When in vectored interrupt mode (`mtvec.mode=1`), the `mtvec.base`
    handler address must be 128-byte aligned.

- On reset, the core is in direct interrupt mode.

## Timer Interrupts

These occur as described in the RISC-V PRA.

- When the `mtimecmp` memory mapped register contains a value greater
  than the `mtime` memory mapped register, a machine timer interrupt
  is posted.

- If interrupts are enabled globally (`mstatus.mie`), and the
  timer interrupt is also enabled (`mstatus.mtie`), then control
  flow is transfered to the trap vector handler at `mtvec.`

- A machine timer interrupt is identified through the `mcause` register
  value `7`, with the `mcause.interrupt` field set to `1`.

All aspects of timer interrupt implementation are handled inside the
core RTL module.
No external interfacing is needed.

## Software interrupts.

These occur as per the PRA, and are triggered by asserting the
`int_software` signal at the core top level.

- If interrupts are enabled globally (`mstatus.mie`), and the
  timer interrupt is also enabled (`mstatus.msie`), then control
  flow is transfered to the trap vector handler at `mtvec.`

- A machine software interrupt is identified through the `mcause` register
  value `3`, with the interrupt field set to `1`.

- It is expected that software must figure out exactly why the interrupt
  was triggered.

## External interrupts.

The SCARV-CPU supports upto 15 external interrupt lines.
An external interrupt is triggered by asserting the `int_external`
pin of the core top level.

- If interrupts are enabled globally (`mstatus.mie`), and the
  timer interrupt is also enabled (`mstatus.meie`), then control
  flow is transfered to the trap vector handler at `mtvec.`

- The top level signal `int_extern_cause` is used to identify which
  hardware peripheral caused the interrupt, and is expected to be
  managed by some external interrupt controller.

  - The value `0` is reserved. If `int_extern_cause` is `0` when
    an external interrupt is triggered, `mcause` takes the value
    `11`, with the interrupt field set.

  - Any non-zero value present on `int_extern_cause` forms the low
    `4` bits of the `mcause` value when the interrupt is taken.
    Bit `5` of `mcause` is always set. Hence the final value of
    `mcause` will be:

    ```
    mcause bit   | 31 | 30 ...  5 | 4 | 3             0  |
    value fields |  1 |     0     | 1 | int_extern_cause |
    ```

    Hence, these interrupt cause codes correspond to those
    *"reserved for platform use*" as per the RISC-V PRA.

  - The cause signal is *not* registered by the core.
    This means that the cause code in `mcause` is the most recent
    value of `int_extern_cause` in the cycle the CPU takes
    the interrupt.

- Platform software is expected to know which peripherals correspond to
  which cause code.

## Non-maskable Interrupts

This is a non-standard feature, which should be used for *critical*
interrupts which must always be serviced.

An NMI is triggered by asserting the top level `int_nmi` pin.

- So long as interrupts are globally enabled (`mstatus.mie`), this
  will immediately transfer control flow to the handler at
  `mtvec`.

- An NMI is identified by the `mcause` code `16`, with the interrupt
  field set.

## Template ASM interrupt handler code

The following code can be coppied into an assembler file, and edited
as appropriate to provied exception and interrupt handling functionality.

```
.global setup_vectored_interrupt_handler
.func setup_vectored_interrupt_handler
setup_vectored_interrupt_handler:
    csrr    a1, mstatus                     // Stash mstatus.
    csrci   mstatus, 0x1                    // Disable interrupts.
    la      a0, vectored_interrupt_handler  // Handler address.
    ori     a0, a0, 0x1                     // Set to vectored mode.
    csrw    mtvec, a0                       // Setup mtvec.
    csrw    mstatus, a1                     // Restore mstatus.
    ret
.endfunc

exception_handler:
    j   exception_handler

interrupt_handler:
    j   interrupt_handler

nmi_handler:
    j   nmi_handler

.balign 128
vectored_interrupt_handler:
.balign 4; j exception_handler // 00 - User SW interrupt / exception
.balign 4; j interrupt_handler // 01 - Supervisor SW interrupt
.balign 4; j interrupt_handler // 02 - Reserved
.balign 4; j interrupt_handler // 03 - Machine SW interrupt
.balign 4; j interrupt_handler // 04 - User Timer Interrupt
.balign 4; j interrupt_handler // 05 - Supervisor Timer Interrupt
.balign 4; j interrupt_handler // 06 - Reserved
.balign 4; j interrupt_handler // 07 - Machine Timer Interrupt
.balign 4; j interrupt_handler // 08 - User External Interrupt
.balign 4; j interrupt_handler // 09 - Supervisor External Interrupt
.balign 4; j interrupt_handler // 10 - Reserved
.balign 4; j interrupt_handler // 11 - Machine External Interrupt
.balign 4; j interrupt_handler // 12 - Reserved
.balign 4; j interrupt_handler // 13 - Reserved
.balign 4; j interrupt_handler // 14 - Reserved
.balign 4; j interrupt_handler // 15 - Reserved
.balign 4; j nmi_handler       // 16 - NMI

```
