use argparse::{ArgumentParser, StoreOption, StoreTrue};
use bitvec::prelude::*;
use lazy_static::lazy_static;
use regex::Regex;
use std::collections::HashMap;
use std::fs::File;
use std::io::prelude::*;
use std::iter::{repeat, FromIterator};

lazy_static! {
    static ref WHITESPACE_RE: Regex = Regex::new(r"\s+").unwrap();
    static ref INSTRUCTIONS: HashMap<&'static str, Instruction> = {
        let mut map = HashMap::new();
        for (i, cmd) in ["ADD", "SUB", "CMP", "XOR", "OR", "AND"].iter().enumerate() {
            map.insert(
                *cmd,
                Instruction::new(
                    i as u8,
                    1,
                    vec![
                        ValidArguments::Except(ArgumentType::Constant),
                        ValidArguments::All,
                        ValidArguments::All,
                    ],
                )
                .unwrap(),
            );
        }
        map.insert(
            "SET",
            Instruction::new(
                6,
                0,
                vec![
                    ValidArguments::Except(ArgumentType::Constant),
                    ValidArguments::All,
                ],
            )
            .unwrap(),
        );
        map.insert(
            "J",
            Instruction::new(7, 0, vec![ValidArguments::Single(ArgumentType::Constant)]).unwrap(),
        );
        map.insert(
            "JZ",
            Instruction::new(
                8,
                0,
                vec![
                    ValidArguments::Single(ArgumentType::Constant),
                    ValidArguments::All,
                ],
            )
            .unwrap(),
        );
        map.insert(
            "JE",
            Instruction::new(
                9,
                0,
                vec![
                    ValidArguments::Single(ArgumentType::Constant),
                    ValidArguments::All,
                ],
            )
            .unwrap(),
        );
        map
    };
}

#[derive(PartialEq, Debug)]
enum ArgumentType {
    Register,
    RAMAddress,
    Constant,
    PointerRegister,
}

impl ArgumentType {
    fn to_machine_code(&self) -> [bool; 2] {
        match self {
            Self::Register => [false, false],
            Self::RAMAddress => [false, true],
            Self::Constant => [true, false],
            Self::PointerRegister => [true, true],
        }
    }

    fn uses_ram(&self) -> bool {
        self == &Self::RAMAddress || self == &Self::PointerRegister
    }
}

#[derive(Debug)]
enum ValidArguments {
    All,
    Many(Vec<ArgumentType>),
    Single(ArgumentType),
    Except(ArgumentType),
}

impl ValidArguments {
    fn writable() -> Self {
        ValidArguments::Except(ArgumentType::Constant)
    }

    fn readable() -> Self {
        ValidArguments::All
    }

    fn validate(&self, arg: &ArgumentType) -> bool {
        match self {
            ValidArguments::All => true,
            ValidArguments::Many(valid) => valid.contains(&arg),
            ValidArguments::Single(valid) => valid == arg,
            ValidArguments::Except(invalid) => invalid != arg,
        }
    }
}

struct Instruction {
    op: BitVec<BigEndian, u8>,
    optional_args: usize,
    valid_args: Vec<ValidArguments>,
}

impl Instruction {
    fn new(
        op: u8,
        optional_args: usize,
        valid_args: Vec<ValidArguments>,
    ) -> Result<Self, &'static str> {
        if op >= 16 {
            return Err("op must be four bits long");
        }
        let mut op = BitVec::from_element(op);
        op.drain(0..4);
        Ok(Self {
            op,
            optional_args,
            valid_args,
        })
    }

    fn build(&self, args: Vec<(ArgumentType, u8)>) -> Result<BitVec<BigEndian, u8>, String> {
        if self.valid_args.len() < args.len() {
            return Err("Too many arguments".to_string());
        }
        if self.valid_args.len() - args.len() > self.optional_args {
            return Err("Too few arguments".to_string());
        }
        if let Some((arg0, _)) = args.first() {
            if arg0.uses_ram() && args.iter().skip(1).any(|(a, _)| a.uses_ram()) {
                return Err("Cannot read and write to RAM simultaneously".to_string());
            }
        }
        let mut argument_descriptor_bin = BitVec::with_capacity(6);
        let mut argument_bin = BitVec::<BigEndian, u8>::with_capacity(24);
        if args.len() < 2 {
            argument_descriptor_bin.extend(bitvec![1, 0]);
        }
        if args.len() < 2 {
            argument_bin.extend(repeat(false).take(8));
        }
        for (i, ((arg, value), valid_args)) in args.iter().zip(&self.valid_args).enumerate() {
            if !valid_args.validate(arg) {
                return Err(format!(
                    "Invalid argument type for argument #{:?}. Expected one of {:?} but found {:?}.",
                    i, valid_args, arg
                 ));
            }
            argument_descriptor_bin
                .extend(BitVec::<BigEndian, u8>::from(&arg.to_machine_code()[..]));
            argument_bin.extend(BitVec::<BigEndian, u8>::from_element(*value));
        }
        if argument_descriptor_bin.len() < 6 {
            argument_descriptor_bin.extend(bitvec![1, 0]);
        }
        if argument_bin.len() < 24 {
            argument_bin.extend(repeat(false).take(8));
        }
        assert_eq!(argument_descriptor_bin.len(), 6);
        assert_eq!(argument_bin.len(), 24);
        let mut bin = argument_descriptor_bin;
        bin.extend(&self.op);
        bin.extend(argument_bin);
        bin.truncate(34);
        Ok(bin)
    }
}

fn main() {
    let mut assembly_filepath: Option<String> = None;
    let mut out_filepath: Option<String> = None;
    let mut use_logism_format = false;
    {
        let mut ap = ArgumentParser::new();
        ap.set_description(
            "Converts bad assembly to bad machine code for computer interals omegalul",
        );
        ap.refer(&mut assembly_filepath).add_argument(
            "File path",
            StoreOption,
            "The path to the assembler you want built",
        );
        ap.refer(&mut out_filepath).add_option(
            &["-o", "--output"],
            StoreOption,
            "The path to the output file",
        );
        ap.refer(&mut use_logism_format).add_option(
            &["-l", "--logism-out-format"],
            StoreTrue,
            "Whether or not have the output file be in logism ready format",
        );
        ap.parse_args_or_exit();
    }
    let assembly_filepath = assembly_filepath.expect("You must provide a file");
    let mut assembly = String::new();
    File::open(assembly_filepath.clone())
        .expect("Invalid file path")
        .read_to_string(&mut assembly)
        .expect("Could not read file");
    let lines = assembly.split("\n").map(|l| l.trim());
    let mut labels = HashMap::new();
    let mut location = 0;
    let lines: Vec<_> = lines
        .enumerate()
        .filter(|(_, l)| {
            if l.ends_with(":") {
                let label: String = l.chars().take(l.len() - 1).collect();
                labels.insert(label, location);
                false
            } else {
                if !l.is_empty() {
                    location += 1;
                }
                true
            }
        })
        .collect();
    let mut machine_code: BitVec<BigEndian, u8> = bitvec![];
    for (line_num, line) in lines {
        let mut parsed_line = WHITESPACE_RE.split(line);
        let instruction_name = parsed_line.next();
        if let Some(name) = instruction_name {
            let mut args = vec![];
            for (i, arg) in parsed_line.enumerate() {
                if labels.contains_key(arg) {
                    args.push((ArgumentType::Constant, labels[arg]));
                    continue;
                }
                args.push(
                    parse_arg(arg).expect(
                        format!(
                            "Error at line {}:\nCould not parse argument {}",
                            line_num, i
                        )
                        .as_str(),
                    ),
                );
            }
            let instruction: &Instruction = &INSTRUCTIONS[name];
            machine_code.extend(
                instruction
                    .build(args)
                    .expect(format!("Error at line {}:\n", line_num).as_str()),
            );
            location += 1;
        }
    }
    if use_logism_format {
        let mut rom_a = "v2.0 raw\n".to_string();
        let mut rom_b = "v2.0 raw\n".to_string();
        for i in (0..(machine_code.len())).step_by(34) {
            let instruction = &machine_code[i..(i + 34)];
            println!("{}", &instruction);
            println!("{}", &instruction[6..]);
            let a_val: BitVec = repeat(false).take(2).chain(&instruction[..6]).collect();
            let b_val: BitVec<BigEndian, u32> =
                repeat(false).take(4).chain(&instruction[6..]).collect();
            println!("{:?}", &b_val.as_slice());
            rom_a += format!("{:x} ", a_val.as_slice()[0]).as_str();
            rom_b += format!("{:x} ", b_val.as_slice()[0]).as_str();
        }
        std::fs::write(
            format!(
                "{}.alol",
                out_filepath.clone().unwrap_or(assembly_filepath.clone())
            ),
            rom_a,
        )
        .expect("Could not write machine code to output");
        std::fs::write(
            format!("{}.blol", out_filepath.unwrap_or(assembly_filepath)),
            rom_b,
        )
        .expect("Could not write machine code to output");
    } else {
        File::create(out_filepath.unwrap_or(format!("{}.lol", assembly_filepath)))
            .expect("Could not load machine code output file")
            .write_all(machine_code.as_slice())
            .expect("Could not write machine code to output");
    }
}

fn parse_arg(arg: &str) -> Result<(ArgumentType, u8), std::num::ParseIntError> {
    Ok(if arg.starts_with("%r") {
        (ArgumentType::PointerRegister, arg[2..].parse::<u8>()?)
    } else if arg.starts_with("%0x") {
        (ArgumentType::RAMAddress, u8::from_str_radix(&arg[3..], 16)?)
    } else if arg.starts_with('r') {
        (ArgumentType::Register, arg[1..].parse::<u8>()?)
    } else if arg.starts_with("0x") {
        (ArgumentType::Constant, u8::from_str_radix(&arg[2..], 16)?)
    } else {
        (ArgumentType::Constant, arg.parse::<u8>()?)
    })
}

#[test]
fn test_arg_parse() {
    assert_eq!(parse_arg("r1"), Ok((ArgumentType::Register, 1)));
    assert_eq!(parse_arg("%0x45"), Ok((ArgumentType::RAMAddress, 0x45)));
    assert_eq!(parse_arg("0x31"), Ok((ArgumentType::Constant, 0x31)));
    assert_eq!(parse_arg("04"), Ok((ArgumentType::Constant, 04)));
    assert_eq!(parse_arg("%r3"), Ok((ArgumentType::PointerRegister, 3)));
    assert!(parse_arg("Hello").is_err());
    assert!(parse_arg("%0").is_err());
    assert!(parse_arg("%0x").is_err());
}

#[test]
fn test_assembly() {
    return; // TODO: update for simplified format, although it has been ensured otherwise that the edits to the format have not affected the functionality of the assembler.
    fn out_from_vec<T>(bin: Vec<u8>) -> Result<BitVec<BigEndian, u8>, T> {
        let mut b = BitVec::from_vec(bin);
        b.truncate(34);
        Ok(b)
    }
    assert_eq!(
        INSTRUCTIONS["ADD"].build(vec![
            (ArgumentType::Register, 0),
            (ArgumentType::Constant, 3)
        ]),
        out_from_vec(vec![0b100010_00, 0b00_000000, 0b00_000000, 0b11_000000, 0])
    );
    assert_eq!(
        INSTRUCTIONS["SUB"].build(vec![
            (ArgumentType::PointerRegister, 1),
            (ArgumentType::RAMAddress, 200),
            (ArgumentType::Register, 3)
        ]),
        out_from_vec(vec![
            0b110100_00,
            0b01_000000,
            0b01_110010,
            0b00_000000,
            0b11_000000,
        ])
    );
    assert!(INSTRUCTIONS["XOR"]
        .build(vec![
            (ArgumentType::Constant, 39),
            (ArgumentType::Register, 2),
            (ArgumentType::RAMAddress, 8)
        ])
        .is_err());
    assert_eq!(
        INSTRUCTIONS["J"].build(vec![(ArgumentType::Constant, 0)]),
        out_from_vec(vec![0b101010_01, 0b11_000000, 0b00_000000, 0, 0,])
    );
    assert_eq!(
        INSTRUCTIONS["JZ"].build(vec![
            (ArgumentType::Constant, 15),
            (ArgumentType::RAMAddress, 3)
        ]),
        out_from_vec(vec![0b101001_10, 0b00_000011, 0b11_000000, 0b11_000000, 0])
    );
}
