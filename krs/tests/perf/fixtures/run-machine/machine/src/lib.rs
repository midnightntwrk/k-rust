//! The long-run benchmark's machine: the CPU group beside a program ROM and a memory map.
//!
//! The rules here answer what the CPU asks of its holder (`cpu::Bus`): a read from the ROM or
//! from `memory`, a write, and the interrupt lines.
//! Each request and its answer are rewrite steps of their own.

use k::Term;
use k::builtin::{Bool, Bytes, Int, Map, bytes};

use cpu::{Bus, Cpu, IRQ_ENABLE, IRQ_REQUEST, Phase};

/// The I/O register the benchmark's program polls. Nothing writes it.
#[k::constant]
pub const STATUS: Int = 0xFF44;

#[k::configuration]
pub struct Machine {
    #[k::cell(nested)]
    pub cpu: Cpu,
    /// The program: read-only, at addresses 0 up to its length.
    #[k::cell]
    pub rom: Bytes,
    /// The end of the ROM region: the program's length.
    #[k::cell(name = "romEnd")]
    pub rom_end: Int,
    /// Every other address, as a map from address to byte. A read of an address the map does
    /// not hold is stuck.
    #[k::cell]
    pub memory: Map<Int, Int>,
}

impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PROGRAM", main)] program: Bytes) -> Self {
        Self {
            cpu: Cpu {
                k: k::k![Phase::Boundary],
                regs: k::map![0 -> 0, 1 -> 0, 2 -> 0, 3 -> 0, 4 -> 0, 5 -> 0, 6 -> 0, 7 -> 0],
                zero: false,
                carry: false,
                pc: 0,
                ime: false,
                t: 0,
                u: 0,
                log: k::builtin::list::empty(),
            },
            rom: program,
            rom_end: bytes::length(program),
            // The I/O registers: memory holds nothing else until the program writes it.
            memory: k::map![IRQ_REQUEST -> 0, IRQ_ENABLE -> 0, STATUS -> 0],
        }
    }
}

/// Whether `addr` is in the ROM region.
#[k::function(total, internal)]
pub fn InRom(rom_end: Term<Int>, addr: Term<Int>) -> Term<Bool> {
    0 <= addr && addr < rom_end
}

k::rules! {
    for Machine;

    /// A read outside the ROM returns the byte `memory` holds.
    #[k::requires(!InRom(rom_end, addr))]
    bus_read: {
        k: [Bus::Read { addr, dest }, ..],
        rom_end,
        memory: { addr -> value, .. },
    } => {
        k: [Bus::Reply { addr, value, dest }, ..],
    };

    /// As `bus_read`, reading the ROM.
    #[k::requires(InRom(rom_end, addr))]
    bus_read_rom: {
        k: [Bus::Read { addr, dest }, ..],
        rom,
        rom_end,
    } => {
        k: [Bus::Reply { addr, value: bytes::get(rom, addr), dest }, ..],
    };

    /// A write outside the ROM stores the byte, at an address the map holds or not.
    #[k::requires(!InRom(rom_end, addr))]
    bus_write: {
        k: [Bus::Write { addr, value }, ..],
        rom_end,
        memory,
    } => {
        k: [..],
        memory: k::map![addr -> value, ..memory],
    };

    /// A write to the ROM changes nothing.
    #[k::requires(InRom(rom_end, addr))]
    bus_write_rom: {
        k: [Bus::Write { addr, value: _ }, ..],
        rom_end,
    } => {
        k: [..],
    };

    /// The interrupt lines are two bytes of `memory`.
    irq_sample: {
        k: [Bus::IrqSample, ..],
        memory,
    } => {
        k: [Bus::IrqLines { enable: memory[IRQ_ENABLE], request: memory[IRQ_REQUEST] }, ..],
    };

    irq_ack: {
        k: [Bus::IrqAck { bits }, ..],
        memory,
    } => {
        k: [..],
        memory: k::map![IRQ_REQUEST -> memory[IRQ_REQUEST] - bits, ..memory],
    };
}
