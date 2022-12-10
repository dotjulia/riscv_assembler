use riscvemitter::{basic::PackedInstruction, rv32i::RV32I};

pub struct Program {
    pub mem: Vec<PackedInstruction>,
}

#[test]
fn test_lw() {
    assert_eq!(
        Into::<u32>::into(RV32I::lw(3.into(), 2.into(), 3.into())),
        Program::parse("lw 3, 3, 2").unwrap().mem[0].into()
    );
}

#[test]
fn test_add() {
    assert_eq!(
        Into::<u32>::into(RV32I::add(2.into(), 1.into(), 3.into())),
        Program::parse("add 3, 1, 2").unwrap().mem[0].into()
    )
}

#[test]
fn test_sw() {
    assert_eq!(
        Into::<u32>::into(RV32I::sw(3.into(), 2.into(), 0.into())),
        Program::parse("sw 3, 2, 0").unwrap().mem[0].into()
    )
}

#[test]
fn test_beq() {
    assert_eq!(
        Into::<u32>::into(RV32I::beq(65.into(), 2.into(), 3.into())),
        Program::parse("beq 3, 2, 65").unwrap().mem[0].into()
    )
}

#[test]
fn test_jal() {
    assert_eq!(
        Into::<u32>::into(RV32I::jal(0.into(), 3.into())),
        Program::parse("jal 3, 0").unwrap().mem[0].into()
    )
}

#[test]
fn test_jalr() {
    assert_eq!(
        Into::<u32>::into(RV32I::jalr(0.into(), 3.into(), 2.into())),
        Program::parse("jalr 2, 0, 3").unwrap().mem[0].into()
    )
}

#[test]
fn test_lui() {
    assert_eq!(
        Into::<u32>::into(RV32I::lui(0.into(), 3.into())),
        Program::parse("lui 3, 0").unwrap().mem[0].into()
    )
}

macro_rules! iinstparser {
    ($name:ident, $words:ident, $prog:ident, $line:ident) => {
        {
            let rd = $words.next();
            let imm = $words.next();
            let rs1 = $words.next();
            if let (Some(rd), Some(imm), Some(rs1)) = (rd, imm, rs1) {
                let rd = rd.trim_end_matches(",").parse::<u32>();
                let imm = imm.trim_end_matches(",").parse::<u32>();
                let rs1 = rs1.trim_end_matches(",").parse::<u32>();
                if let (Ok(rd), Ok(imm), Ok(rs1)) = (rd, imm, rs1) {
                    let inst = RV32I::$name(imm.into(), rs1.into(), rd.into());
                    $prog.push(inst);
                } else {
                    return Err(format!("Failed parsing argument: {}", $line));
                }
            } else {
                return Err(format!("Invalid instruction: {}", $line).to_string());
            }
        }
    };
}

macro_rules! rinstparser {
    ($name:ident, $words:ident, $prog:ident, $line:ident) => {
        {
            let rd = $words.next();
            let rs1 = $words.next();
            let rs2 = $words.next();
            if let (Some(rd), Some(rs1), Some(rs2)) = (rd, rs1, rs2) {
                let rd = rd.trim_end_matches(",").parse::<u32>();
                let rs1 = rs1.trim_end_matches(",").parse::<u32>();
                let rs2 = rs2.trim_end_matches(",").parse::<u32>();
                if let (Ok(rd), Ok(rs1), Ok(rs2)) = (rd, rs1, rs2) {
                    let inst = RV32I::$name(rs2.into(), rs1.into(), rd.into());
                    $prog.push(inst);
                } else {
                    return Err(format!("Failed parsing argument: {}", $line));
                }
            } else {
                return Err(format!("Invalid instruction: {}", $line).to_string());
            }
        }
    };
}

macro_rules! sinstparser {
    ($name:ident, $words:ident, $prog:ident, $line:ident) => {
        {
            let rs2 = $words.next();
            let imm = $words.next();
            let rs1 = $words.next();
            if let (Some(rs2), Some(imm), Some(rs1)) = (rs2, imm, rs1) {
                let rs2 = rs2.trim_end_matches(",").parse::<u32>();
                let imm = imm.trim_end_matches(",").parse::<u32>();
                let rs1 = rs1.trim_end_matches(",").parse::<u32>();
                if let (Ok(rs2), Ok(imm), Ok(rs1)) = (rs2, imm, rs1) {
                    let inst = RV32I::$name(rs2.into(), imm.into(), rs1.into());
                    $prog.push(inst);
                } else {
                    return Err(format!("Failed parsing argument: {}", $line));
                }
            } else {
                return Err(format!("Invalid instruction: {}", $line).to_string());
            }
        }
    };
}

macro_rules! binstparser {
    ($name:ident, $words:ident, $prog:ident, $line:ident) => {
        {
            let rs1 = $words.next();
            let rs2 = $words.next();
            let imm = $words.next();
            if let (Some(rs1), Some(rs2), Some(imm)) = (rs1, rs2, imm) {
                let rs1 = rs1.trim_end_matches(",").parse::<u32>();
                let rs2 = rs2.trim_end_matches(",").parse::<u32>();
                let imm = imm.trim_end_matches(",").parse::<u32>();
                if let (Ok(rs1), Ok(rs2), Ok(imm)) = (rs1, rs2, imm) {
                    let inst = RV32I::$name(imm.into(), rs2.into(), rs1.into());
                    $prog.push(inst);
                } else {
                    return Err(format!("Failed parsing argument: {}", $line));
                }
            } else {
                return Err(format!("Invalid instruction: {}", $line).to_string());
            }
        }
    };
}
macro_rules! jinstparser {
    ($name:ident, $words:ident, $prog:ident, $line:ident) => {
        {
            let rd = $words.next();
            let imm = $words.next();
            if let (Some(rd), Some(imm)) = (rd, imm) {
                let rd = rd.trim_end_matches(",").parse::<u32>();
                let imm = imm.trim_end_matches(",").parse::<u32>();
                if let (Ok(rd), Ok(imm)) = (rd, imm) {
                    let inst = RV32I::$name(imm.into(), rd.into());
                    $prog.push(inst);
                } else {
                    return Err(format!("Failed parsing argument: {}", $line));
                }
            } else {
                return Err(format!("Invalid instruction: {}", $line).to_string());
            }
        }
    };
}

macro_rules! uinstparser {
    ($name:ident, $words:ident, $prog:ident, $line:ident) => {
        {
            let rd = $words.next();
            let imm = $words.next();
            if let (Some(rd), Some(imm)) = (rd, imm) {
                let rd = rd.trim_end_matches(",").parse::<u32>();
                let imm = imm.trim_end_matches(",").parse::<u32>();
                if let (Ok(rd), Ok(imm)) = (rd, imm) {
                    let inst = RV32I::$name(imm.into(), rd.into());
                    $prog.push(inst);
                } else {
                    return Err(format!("Failed parsing argument: {}", $line));
                }
            } else {
                return Err(format!("Invalid instruction: {}", $line).to_string());
            }
        }
    };
}

impl Program {
    pub fn parse(input: &str) -> Result<Program, String> {
        let lines = input.split("\n").collect::<Vec<&str>>();
        let mut prog: Vec<PackedInstruction> = Vec::new();
        for line in lines {
            let mut words = line.split_whitespace();
            let op = words.next();
            if let Some(op) = op {
                match op {
                    "jalr" => iinstparser!(jalr, words, prog, line),
                    "lb" => iinstparser!(lb, words, prog, line),
                    "lh" => iinstparser!(lh, words, prog, line),
                    "lw" => iinstparser!(lw, words, prog, line),
                    "lbu" => iinstparser!(lbu, words, prog, line),
                    "lhu" => iinstparser!(lhu, words, prog, line),
                    "addi" => iinstparser!(addi, words, prog, line),
                    "slti" => iinstparser!(slti, words, prog, line),
                    "sltiu" => iinstparser!(sltiu, words, prog, line),
                    "xori" => iinstparser!(xori, words, prog, line),
                    "ori" => iinstparser!(ori, words, prog, line),
                    "andi" => iinstparser!(andi, words, prog, line),
                    "ebreak" => prog.push(RV32I::ebreak()),
                    "ecall" => prog.push(RV32I::ecall()),
                    "slli" => rinstparser!(slli, words, prog, line),
                    "srli" => rinstparser!(srli, words, prog, line),
                    "srai" => rinstparser!(srai, words, prog, line),
                    "add" => rinstparser!(add, words, prog, line),
                    "sub" => rinstparser!(sub, words, prog, line),
                    "sll" => rinstparser!(sll, words, prog, line),
                    "slt" => rinstparser!(slt, words, prog, line),
                    "sltu" => rinstparser!(sltu, words, prog, line),
                    "xor" => rinstparser!(xor, words, prog, line),
                    "srl" => rinstparser!(srl, words, prog, line),
                    "sra" => rinstparser!(sra, words, prog, line),
                    "or" => rinstparser!(or, words, prog, line),
                    "and" => rinstparser!(and, words, prog, line),
                    "sw" => sinstparser!(sw, words, prog, line),
                    "sh" => sinstparser!(sh, words, prog, line),
                    "sb" => sinstparser!(sb, words, prog, line),
                    "beq" => binstparser!(beq, words, prog, line),
                    "bne" => binstparser!(bne, words, prog, line),
                    "blt" => binstparser!(blt, words, prog, line),
                    "bge" => binstparser!(bge, words, prog, line),
                    "bltu" => binstparser!(bltu, words, prog, line),
                    "bgeu" => binstparser!(bgeu, words, prog, line),
                    "jal" => jinstparser!(jal, words, prog, line),
                    "lui" => uinstparser!(lui, words, prog, line),
                    "auipc" => uinstparser!(auipc, words, prog, line),
                    "\n" => continue,
                    _ => return Err(format!("Unknown instruction: {}", op)),
                }
            }
        }
        Ok(Program { mem: prog })
    }
}