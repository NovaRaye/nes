use bitflags::bitflags;
use std::collections::HashMap;

use crate::{bus::Bus, opcodes};

bitflags! {
    #[derive(Clone)]
    pub struct CpuFlags: u8 {
        const CARRY             = 0b00000001;
        const ZERO              = 0b00000010;
        const INTERRUPT_DISABLE = 0b00000100;
        const DECIMAL_MODE      = 0b00001000;
        const BREAK             = 0b00010000;
        const BREAK2            = 0b00100000;
        const OVERFLOW          = 0b01000000;
        const NEGATIV           = 0b10000000;
    }
}

pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub stack_pointer: u8,
    pub status: CpuFlags,
    pub program_counter: u16,
    pub bus: Bus,
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

const STACK: u16 = 0x0100;
const STACK_RESET: u8 = 0xfd;

pub trait Mem {
    fn mem_read(&self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);

    fn mem_read_u16(&self, pos: u16) -> u16 {
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | (lo as u16)
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }
}

impl Mem for CPU {
    fn mem_read(&self, addr: u16) -> u8 {
        self.bus.mem_read(addr)
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.bus.mem_write(addr, data)
    }
}

impl CPU {
    pub fn new(bus: Bus) -> CPU {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            stack_pointer: STACK_RESET,
            status: CpuFlags::from_bits_truncate(0b00100100),
            program_counter: 0x8000,
            bus,
        }
    }

    pub fn load(&mut self, program: Vec<u8>) {
        for i in 0..(program.len() as u16) {
            self.mem_write(0x0000 + i, program[i as usize]);
        }
        self.mem_write_u16(0xFFFC, 0x0000);
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.status = CpuFlags::from_bits_truncate(0b00100100);
        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run()
    }

    fn plp(&mut self) {
        let value = self.stack_pop();
        self.status = CpuFlags::from_bits_truncate(value);
        self.status.remove(CpuFlags::BREAK);
        self.status.insert(CpuFlags::BREAK2);
    }

    fn php(&mut self) {
        let mut flags = self.status.clone();
        flags.insert(CpuFlags::BREAK);
        flags.insert(CpuFlags::BREAK2);
        self.stack_push(flags.bits());
    }

    fn stack_pop(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        self.mem_read((STACK as u16) + self.stack_pointer as u16)
    }

    fn stack_push(&mut self, value: u8) {
        self.mem_write(STACK + self.stack_pointer as u16, value);
        self.stack_pointer = self.stack_pointer.wrapping_sub(1);
    }

    fn set_register_a(&mut self, value: u8) {
        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        if result == 0 {
            self.status.insert(CpuFlags::ZERO);
        } else {
            self.status.remove(CpuFlags::ZERO);
        }

        if result & 0b1000_0000 != 0 {
            self.status.insert(CpuFlags::NEGATIV);
        } else {
            self.status.remove(CpuFlags::NEGATIV);
        }
    }

    pub fn get_absolute_address(&self, mode: &AddressingMode, addr: u16) -> u16 {
        match mode {
            AddressingMode::ZeroPage => self.mem_read(addr) as u16,

            AddressingMode::Absolute => self.mem_read_u16(addr),

            AddressingMode::ZeroPage_X => {
                let pos = self.mem_read(addr);
                let addr = pos.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPage_Y => {
                let pos = self.mem_read(addr);
                let addr = pos.wrapping_add(self.register_y) as u16;
                addr
            }

            AddressingMode::Absolute_X => {
                let base = self.mem_read_u16(addr);
                let addr = base.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::Absolute_Y => {
                let base = self.mem_read_u16(addr);
                let addr = base.wrapping_add(self.register_y as u16);
                addr
            }

            AddressingMode::Indirect_X => {
                let base = self.mem_read(addr);

                let ptr: u8 = (base as u8).wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16);
                let hi = self.mem_read(ptr.wrapping_add(1) as u16);
                (hi as u16) << 8 | (lo as u16)
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(addr);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read((base as u8).wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);
                let deref = deref_base.wrapping_add(self.register_y as u16);
                deref
            }

            _ => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            _ => self.get_absolute_address(mode, self.program_counter),
        }
    }
    fn pla(&mut self) {
        let value = self.stack_pop();
        self.set_register_a(value);
    }

    fn add_to_register_a(&mut self, data: u8) {
        let sum = self.register_a as u16
            + data as u16
            + (if self.status.contains(CpuFlags::CARRY) {
                1
            } else {
                0
            }) as u16;

        let carry = sum > 0xff;

        if carry {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        let result = sum as u8;

        if (data ^ result) & (result ^ self.register_a) & 0x80 != 0 {
            self.status.insert(CpuFlags::OVERFLOW);
        } else {
            self.status.remove(CpuFlags::OVERFLOW)
        }

        self.set_register_a(result);
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.add_to_register_a(value);
    }

    fn sbc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let data = self.mem_read(addr);
        self.add_to_register_a(((data as i8).wrapping_neg().wrapping_sub(1)) as u8);
    }

    fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.set_register_a(self.register_a & value);
    }

    fn eor(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.set_register_a(self.register_a ^ value);
    }

    fn ora(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.set_register_a(self.register_a | value);
    }

    fn lsr_accumulator(&mut self) {
        let mut data = self.register_a;
        if data & 1 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        data = data >> 1;
        self.set_register_a(data)
    }

    fn lsr(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        if data & 1 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        data = data >> 1;
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn asl_accumulator(&mut self) {
        let mut data = self.register_a;
        if data >> 7 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        data = data << 1;
        self.set_register_a(data);
    }

    fn asl(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        if data >> 7 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        data = data << 1;
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn rol_accumulator(&mut self) {
        let mut data = self.register_a;
        let old_carry = self.status.contains(CpuFlags::CARRY);

        if data >> 7 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        data = data << 1;
        if old_carry {
            data = data | 1;
        }
        self.set_register_a(data);
    }

    fn rol(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        let old_carry = self.status.contains(CpuFlags::CARRY);

        if data >> 7 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        data = data << 1;
        if old_carry {
            data = data | 1;
        }
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn ror_accumulator(&mut self) {
        let mut data = self.register_a;
        let old_carry = self.status.contains(CpuFlags::CARRY);

        if data & 1 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        data = data >> 1;
        if old_carry {
            data = data | 0b1000_0000;
        }
        self.set_register_a(data);
    }

    fn ror(&mut self, mode: &AddressingMode) -> u8{
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        let old_carry = self.status.contains(CpuFlags::CARRY);

        if data & 1 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }
        data = data >> 1;
        if old_carry {
            data = data | 0b1000_0000;
        }
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn inc(&mut self, mode: &AddressingMode) -> u8 {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        data = data.wrapping_add(1);
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
        data
    }

    fn iny(&mut self) {
        self.register_y = self.register_y.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn dec(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        data = data.wrapping_sub(1);
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
    }

    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn compare(&mut self, mode: &AddressingMode, register: u8) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        if register >= value {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        let result = register.wrapping_sub(value);
        self.update_zero_and_negative_flags(result);
    }

    fn jmp_absolute(&mut self) {
        let mem_address = self.mem_read_u16(self.program_counter);
        self.program_counter = mem_address;
    }

    fn jmp_indirect(&mut self) {
        let mem_address = self.mem_read_u16(self.program_counter);
        let indirect_ref = if mem_address & 0x00FF == 0x00FF {
            let lo = self.mem_read(mem_address);
            let hi = self.mem_read(mem_address & 0xFF00);
            (hi as u16) << 8 | (lo as u16)
        } else {
            self.mem_read_u16(mem_address)
        };
        self.program_counter = indirect_ref;
    }

    fn stack_push_u16(&mut self, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.stack_push(hi);
        self.stack_push(lo);
    }

    fn jsr(&mut self) {
        self.stack_push_u16(self.program_counter + 2 - 1);
        let target_address = self.mem_read_u16(self.program_counter);
        self.program_counter = target_address
    }

    fn stack_pop_u16(&mut self) -> u16 {
        let lo = self.stack_pop() as u16;
        let hi = self.stack_pop() as u16;
        hi << 8 | lo
    }

    fn branch(&mut self, condition: bool) {
        if condition {
            let jump: i8 = self.mem_read(self.program_counter) as i8;
            let jump_addr = self
                .program_counter
                .wrapping_add(1)
                .wrapping_add(jump as u16);

            self.program_counter = jump_addr;
        }
    }

    fn bit(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let result = self.register_a & value;
        if result == 0 {
            self.status.insert(CpuFlags::ZERO);
        } else {
            self.status.remove(CpuFlags::ZERO);
        }

        if value & 0b1000_0000 != 0 {
            self.status.insert(CpuFlags::NEGATIV);
        } else {
            self.status.remove(CpuFlags::NEGATIV);
        }

        if value & 0b0100_0000 != 0 {
            self.status.insert(CpuFlags::OVERFLOW);
        } else {
            self.status.remove(CpuFlags::OVERFLOW);
        }
    }

    fn stx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_x);
    }

    fn sty(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_y);
    }

    fn ldx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_x = value;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn ldy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_y = value;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn tay(&mut self) {
        self.register_y = self.register_a;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn tsx(&mut self) {
        self.register_x = self.stack_pointer;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn tya(&mut self) {
        self.register_a = self.register_y;
        self.update_zero_and_negative_flags(self.register_a);
    }

    pub fn run(&mut self) {
        self.run_with_callback(|_| {});
    }

    pub fn and_with_register_a(&mut self, data: u8) {
        self.set_register_a(data & self.register_a);
    }

    pub fn or_with_register_a(&mut self, data: u8) {
        self.set_register_a(data | self.register_a);
    }

    pub fn sub_from_register_a(&mut self, data: u8) {
        self.add_to_register_a(((data as i8).wrapping_neg().wrapping_sub(1)) as u8);
    }

    pub fn xor_with_register_a(&mut self, data: u8) {
        self.set_register_a(data ^ self.register_a);
    }

    pub fn run_with_callback<F>(&mut self, mut callback: F)
    where
        F: FnMut(&mut CPU),
    {
        let ref opcodes: HashMap<u8, &'static opcodes::OpCode> = *opcodes::OPCODES_MAP;

        loop {
            callback(self);
            let code = self.mem_read(self.program_counter);
            let opcode = opcodes
                .get(&code)
                .expect(&format!("OpCode {:x} is not recognized", code));
            self.program_counter += 1;
            let program_counter_state = self.program_counter;
            match code {
                0xA9 | 0xA5 | 0xB5 | 0xAD | 0xBD | 0xB9 | 0xA1 | 0xB1 => {
                    self.lda(&opcode.mode);
                }
                0x85 | 0x95 | 0x8D | 0x9D | 0x99 | 0x81 | 0x91 => {
                    self.sta(&opcode.mode);
                }
                0xAA => self.tax(),
                0xE8 => self.inx(),
                // CLD
                0xD8 => self.status.remove(CpuFlags::DECIMAL_MODE),
                // CLI
                0x58 => self.status.remove(CpuFlags::INTERRUPT_DISABLE),
                // CLV
                0xB8 => self.status.remove(CpuFlags::OVERFLOW),
                // CLC
                0x18 => self.status.remove(CpuFlags::CARRY),
                // SEC
                0x38 => self.status.insert(CpuFlags::CARRY),
                // SEI
                0x78 => self.status.insert(CpuFlags::INTERRUPT_DISABLE),
                // SED
                0xF8 => self.status.insert(CpuFlags::DECIMAL_MODE),
                // PHA
                0x48 => self.stack_push(self.register_a),
                // PLA
                0x68 => self.pla(),
                // PHP
                0x08 => self.php(),
                // PLP
                0x28 => self.plp(),
                // ADC
                0x69 | 0x65 | 0x75 | 0x6D | 0x7D | 0x79 | 0x61 | 0x71 => {
                    self.adc(&opcode.mode);
                }
                // SBC
                0xE9 | 0xE5 | 0xF5 | 0xED | 0xFD | 0xF9 | 0xE1 | 0xF1 => {
                    self.sbc(&opcode.mode);
                }
                // AND
                0x29 | 0x25 | 0x35 | 0x2D | 0x3D | 0x39 | 0x21 | 0x31 => {
                    self.and(&opcode.mode);
                }
                // EOR
                0x49 | 0x45 | 0x55 | 0x4D | 0x5D | 0x59 | 0x41 | 0x51 => {
                    self.eor(&opcode.mode);
                }
                // ORA
                0x09 | 0x05 | 0x15 | 0x0D | 0x1D | 0x19 | 0x01 | 0x11 => {
                    self.ora(&opcode.mode);
                }
                // LSR
                0x4A => self.lsr_accumulator(),
                0x46 | 0x56 | 0x4E | 0x5E => {
                    self.lsr(&opcode.mode);
                }
                // ASL
                0x0A => self.asl_accumulator(),
                0x06 | 0x16 | 0x0E | 0x1E => {
                    self.asl(&opcode.mode);
                }
                // ROL
                0x2A => self.rol_accumulator(),
                0x26 | 0x36 | 0x2E | 0x3E => {
                    self.rol(&opcode.mode);
                }
                // ROR
                0x6A => self.ror_accumulator(),
                0x66 | 0x76 | 0x6E | 0x7E => {
                    self.ror(&opcode.mode);
                }
                // INC
                0xE6 | 0xF6 | 0xEE | 0xFE => {
                    self.inc(&opcode.mode);
                }
                // INY
                0xC8 => {
                    self.iny();
                }
                // DEC
                0xC6 | 0xD6 | 0xCE | 0xDE => {
                    self.dec(&opcode.mode);
                }
                // DEX
                0xCA => self.dex(),
                // DEY
                0x88 => self.dey(),
                // CMP
                0xC9 | 0xC5 | 0xD5 | 0xCD | 0xDD | 0xD9 | 0xC1 | 0xD1 => {
                    self.compare(&opcode.mode, self.register_a);
                }
                // CPX
                0xE0 | 0xE4 | 0xEC => {
                    self.compare(&opcode.mode, self.register_x);
                }
                // CPY
                0xC0 | 0xC4 | 0xCC => {
                    self.compare(&opcode.mode, self.register_y);
                }
                // JMP
                0x4C => {
                    self.jmp_absolute();
                }
                0x6C => {
                    self.jmp_indirect();
                }
                // JSR
                0x20 => {
                    self.jsr();
                }
                // RTS
                0x60 => {
                    self.program_counter = self.stack_pop_u16() + 1;
                }
                // RTI
                0x40 => {
                    self.status = CpuFlags::from_bits_truncate(self.stack_pop());
                    self.status.remove(CpuFlags::BREAK);
                    self.status.insert(CpuFlags::BREAK2);
                    self.program_counter = self.stack_pop_u16();
                }
                // BNE
                0xD0 => {
                    self.branch(!self.status.contains(CpuFlags::ZERO));
                }
                // BVS
                0x70 => {
                    self.branch(self.status.contains(CpuFlags::OVERFLOW));
                }
                // BVC
                0x50 => {
                    self.branch(!self.status.contains(CpuFlags::OVERFLOW));
                }
                // BPL
                0x10 => {
                    self.branch(!self.status.contains(CpuFlags::NEGATIV));
                }
                // BMI
                0x30 => {
                    self.branch(self.status.contains(CpuFlags::NEGATIV));
                }
                // BEQ
                0xF0 => {
                    self.branch(self.status.contains(CpuFlags::ZERO));
                }
                // BCS
                0xb0 => {
                    self.branch(self.status.contains(CpuFlags::CARRY));
                }
                // BCC
                0x90 => {
                    self.branch(!self.status.contains(CpuFlags::CARRY));
                }
                // BIT
                0x24 | 0x2C => {
                    self.bit(&opcode.mode);
                }
                // STX
                0x86 | 0x96 | 0x8E => {
                    self.stx(&opcode.mode);
                }
                // STY
                0x84 | 0x94 | 0x8C => {
                    self.sty(&opcode.mode);
                }
                // LDX
                0xA2 | 0xA6 | 0xB6 | 0xAE | 0xBE => {
                    self.ldx(&opcode.mode);
                }
                // LDY
                0xA0 | 0xA4 | 0xB4 | 0xAC | 0xBC => {
                    self.ldy(&opcode.mode);
                }
                // NOP
                0xEA => {}
                // TAY
                0xA8 => {
                    self.tay();
                }
                // TSX
                0xBA => {
                    self.tsx();
                }
                // TXA
                0x8A => {
                    self.register_a = self.register_x;
                    self.update_zero_and_negative_flags(self.register_a);
                }

                //  TXS
                0x9a => {
                    self.stack_pointer = self.register_x;
                }

                // TYA
                0x98 => {
                    self.tya();
                }
                0x00 => break,
                // unofficial opcodes
                // https://www.nesdev.org/undocumented_opcodes.txt
                // DCP
                0xC7 | 0xD7 | 0xCF | 0xDF | 0xDB | 0xC3 | 0xD3 => {
                    let addr = self.get_operand_address(&opcode.mode);
                    let mut data = self.mem_read(addr);
                    data = data.wrapping_sub(1);
                    self.mem_write(addr, data);
                    if data <= self.register_a {
                        self.status.insert(CpuFlags::CARRY);
                    }
                    self.update_zero_and_negative_flags(self.register_a.wrapping_sub(data));
                }
                /* RLA */
                0x27 | 0x37 | 0x2F | 0x3F | 0x3b | 0x33 | 0x23 => {
                    let data = self.rol(&opcode.mode);
                    self.and_with_register_a(data);
                }
                 /* SLO */ //todo tests
                 0x07 | 0x17 | 0x0F | 0x1f | 0x1b | 0x03 | 0x13 => {
                    let data = self.asl(&opcode.mode);
                    self.or_with_register_a(data);
                }

                /* SRE */ //todo tests
                0x47 | 0x57 | 0x4F | 0x5f | 0x5b | 0x43 | 0x53 => {
                    let data = self.lsr(&opcode.mode);
                    self.xor_with_register_a(data);
                }

                /* SKB */
                0x80 | 0x82 | 0x89 | 0xc2 | 0xe2 => {
                    /* 2 byte NOP (immediate ) */
                    // todo: might be worth doing the read
                }

                /* AXS */
                0xCB => {
                    let addr = self.get_operand_address(&opcode.mode);
                    let data = self.mem_read(addr);
                    let x_and_a = self.register_x & self.register_a;
                    let result = x_and_a.wrapping_sub(data);

                    if data <= x_and_a {
                        self.status.insert(CpuFlags::CARRY);
                    }
                    self.update_zero_and_negative_flags(result);

                    self.register_x = result;
                }

                /* ARR */
                0x6B => {
                    let addr = self.get_operand_address(&opcode.mode);
                    let data = self.mem_read(addr);
                    self.and_with_register_a(data);
                    self.ror_accumulator();
                    //todo: registers
                    let result = self.register_a;
                    let bit_5 = (result >> 5) & 1;
                    let bit_6 = (result >> 6) & 1;

                    if bit_6 == 1 {
                        self.status.insert(CpuFlags::CARRY)
                    } else {
                        self.status.remove(CpuFlags::CARRY)
                    }

                    if bit_5 ^ bit_6 == 1 {
                        self.status.insert(CpuFlags::OVERFLOW);
                    } else {
                        self.status.remove(CpuFlags::OVERFLOW);
                    }

                    self.update_zero_and_negative_flags(result);
                }

                /* unofficial SBC */
                0xeb => {
                    let addr = self.get_operand_address(&opcode.mode);
                    let data = self.mem_read(addr);
                    self.sub_from_register_a(data);
                }

                /* ANC */
                0x0b | 0x2b => {
                    let addr = self.get_operand_address(&opcode.mode);
                    let data = self.mem_read(addr);
                    self.and_with_register_a(data);
                    if self.status.contains(CpuFlags::NEGATIV) {
                        self.status.insert(CpuFlags::CARRY);
                    } else {
                        self.status.remove(CpuFlags::CARRY);
                    }
                }

                /* ALR */
                0x4b => {
                    let addr = self.get_operand_address(&opcode.mode);
                    let data = self.mem_read(addr);
                    self.and_with_register_a(data);
                    self.lsr_accumulator();
                }

                //todo: test for everything bellow

                /* NOP read */
                0x04 | 0x44 | 0x64 | 0x14 | 0x34 | 0x54 | 0x74 | 0xd4 | 0xf4 | 0x0c | 0x1c
                | 0x3c | 0x5c | 0x7c | 0xdc | 0xfc => {
                    let addr = self.get_operand_address(&opcode.mode);
                    let data = self.mem_read(addr);
                    /* do nothing */
                }

                /* RRA */
                0x67 | 0x77 | 0x6f | 0x7f | 0x7b | 0x63 | 0x73 => {
                    let data = self.ror(&opcode.mode);
                    self.add_to_register_a(data);
                }

                /* ISB */
                0xe7 | 0xf7 | 0xef | 0xff | 0xfb | 0xe3 | 0xf3 => {
                    let data = self.inc(&opcode.mode);
                    self.sub_from_register_a(data);
                }

                /* NOPs */
                0x02 | 0x12 | 0x22 | 0x32 | 0x42 | 0x52 | 0x62 | 0x72 | 0x92 | 0xb2 | 0xd2
                | 0xf2 => { /* do nothing */ }

                0x1a | 0x3a | 0x5a | 0x7a | 0xda | 0xfa => { /* do nothing */ }

                /* LAX */
                0xa7 | 0xb7 | 0xaf | 0xbf | 0xa3 | 0xb3 => {
                    let addr = self.get_operand_address(&opcode.mode);
                    let data = self.mem_read(addr);
                    self.set_register_a(data);
                    self.register_x = self.register_a;
                }

                /* SAX */
                0x87 | 0x97 | 0x8f | 0x83 => {
                    let data = self.register_a & self.register_x;
                    let addr = self.get_operand_address(&opcode.mode);
                    self.mem_write(addr, data);
                }

                /* LXA */
                0xab => {
                    self.lda(&opcode.mode);
                    self.tax();
                }

                /* XAA */
                0x8b => {
                    self.register_a = self.register_x;
                    self.update_zero_and_negative_flags(self.register_a);
                    let addr = self.get_operand_address(&opcode.mode);
                    let data = self.mem_read(addr);
                    self.and_with_register_a(data);
                }

                /* LAS */
                0xbb => {
                    let addr = self.get_operand_address(&opcode.mode);
                    let mut data = self.mem_read(addr);
                    data = data & self.stack_pointer;
                    self.register_a = data;
                    self.register_x = data;
                    self.stack_pointer = data;
                    self.update_zero_and_negative_flags(data);
                }

                /* TAS */
                0x9b => {
                    let data = self.register_a & self.register_x;
                    self.stack_pointer = data;
                    let mem_address =
                        self.mem_read_u16(self.program_counter) + self.register_y as u16;

                    let data = ((mem_address >> 8) as u8 + 1) & self.stack_pointer;
                    self.mem_write(mem_address, data)
                }

                /* AHX  Indirect Y */
                0x93 => {
                    let pos: u8 = self.mem_read(self.program_counter);
                    let mem_address = self.mem_read_u16(pos as u16) + self.register_y as u16;
                    let data = self.register_a & self.register_x & (mem_address >> 8) as u8;
                    self.mem_write(mem_address, data)
                }

                /* AHX Absolute Y*/
                0x9f => {
                    let mem_address =
                        self.mem_read_u16(self.program_counter) + self.register_y as u16;

                    let data = self.register_a & self.register_x & (mem_address >> 8) as u8;
                    self.mem_write(mem_address, data)
                }

                /* SHX */
                0x9e => {
                    let mem_address =
                        self.mem_read_u16(self.program_counter) + self.register_y as u16;

                    // todo if cross page boundry {
                    //     mem_address &= (self.x as u16) << 8;
                    // }
                    let data = self.register_x & ((mem_address >> 8) as u8 + 1);
                    self.mem_write(mem_address, data)
                }

                /* SHY */
                0x9c => {
                    let mem_address =
                        self.mem_read_u16(self.program_counter) + self.register_x as u16;
                    let data = self.register_y & ((mem_address >> 8) as u8 + 1);
                    self.mem_write(mem_address, data)
                }
                _ => todo!(),
            }

            if program_counter_state == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cartridge::test;

    #[test]
    fn test_lda_immediate_load_data() {
        let bus = Bus::new(test::new_test_rom(vec![0xA9, 0x05, 0x00]));
        let mut cpu = CPU::new(bus);
        cpu.run();
        assert_eq!(cpu.register_a, 0x05);
        assert!(cpu.status.bits() & 0b0000_0010 == 0);
        assert!(cpu.status.bits() & 0b1000_0000 == 0);
    }

    #[test]
    fn test_lda_zero_flag() {
        let bus = Bus::new(test::new_test_rom(vec![0xA9, 0x00, 0x00]));
        let mut cpu = CPU::new(bus);
        cpu.run();
        assert!(cpu.status.bits() & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_tax_move_a_to_x() {
        let bus = Bus::new(test::new_test_rom(vec![0xA9, 0x0A, 0xAA, 0x00]));
        let mut cpu = CPU::new(bus);
        cpu.run();

        assert_eq!(cpu.register_x, 10)
    }

    #[test]
    fn test_inx() {
        let bus = Bus::new(test::new_test_rom(vec![0xA9, 0xff, 0xaa, 0xe8, 0xe8, 0x00]));
        let mut cpu = CPU::new(bus);
        cpu.run();
        assert_eq!(cpu.register_x, 1)
    }

    #[test]
    fn test_lda_from_memory() {
        let bus = Bus::new(test::new_test_rom(vec![0xA5, 0x10, 0x00]));
        let mut cpu = CPU::new(bus);
        cpu.mem_write(0x10, 0x55);
        cpu.run();
        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_sta() {
        let bus = Bus::new(test::new_test_rom(vec![0xA9, 0x55, 0x85, 0x10, 0x00]));
        let mut cpu = CPU::new(bus);
        cpu.run();
        assert_eq!(cpu.mem_read(0x10), 0x55);
    }
}
