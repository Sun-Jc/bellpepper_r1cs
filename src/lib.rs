// ! The function `write_r1cs` convert a bellpepper constraint system into a circom r1cs format file
// ! Output variables must be specified by the user, or all public variables will be considered as inputs.
// ! Note: Constant One will be inserted as the first public input, every original input variable id will increase by 1

use bellpepper_core::Index as VIndex;
use bellpepper_core::LinearCombination;
use ff::{PrimeField, PrimeFieldBits};

mod form_cs;
pub use form_cs::*;

type LinComb<T> = Vec<(usize, T)>;
type Constraint<T> = (LinComb<T>, LinComb<T>, LinComb<T>);

#[derive(Debug, Clone, Default)]
pub struct ConstraintSystemWithInputsOutputs<Scalar: PrimeField> {
    num_outputs: usize,
    num_public_inputs: usize,
    num_aux: usize,
    constraints: Vec<Constraint<Scalar>>,
    old_input_id_to_new_id: Vec<usize>,
    old_aux_id_to_new_id: Vec<usize>,
}

impl<Scalar: PrimeField> ConstraintSystemWithInputsOutputs<Scalar> {
    pub fn from_constraint_system(
        outputs: &HashSet<VIndex>,
        num_public_vars: usize,
        num_aux: usize,
        constraints: &[(LinearCombination<Scalar>, LinearCombination<Scalar>, LinearCombination<Scalar>)],
    ) -> Self {
        let num_outputs = outputs.len();

        let mut res = Self {
            num_outputs,
            num_public_inputs: num_public_vars - num_outputs,
            num_aux,
            old_input_id_to_new_id: vec![0; num_public_vars],
            old_aux_id_to_new_id: vec![0; num_aux],
            ..Default::default()
        };

        // fill in the old_input_id_to_new_id
        {
            let mut num_outputs_found = 0;
            let mut num_public_inputs_found = 0;

            for i in 0..num_public_vars {

                if outputs.contains(&VIndex::Input(i)) {
                    res.old_input_id_to_new_id[i] = num_outputs_found;
                    num_outputs_found += 1;
                } else {
                    res.old_input_id_to_new_id[i] = num_outputs + num_public_inputs_found;
                    num_public_inputs_found += 1;
                }
            }
        }

        // fill in the old_aux_id_to_new_id
        {
            for i in 0..num_aux {
                res.old_aux_id_to_new_id[i] = num_public_vars + i;
            }
        }

        // fill in the constraints
        {
            let remap_lc = |source: &LinearCombination<Scalar>| -> LinComb<Scalar> {
                source.iter().map(|(var, coeff)| {
                    match var.0 {
                        VIndex::Input(old_input) => {
                            let new_id = res.old_input_id_to_new_id[old_input];
                            (new_id, *coeff)
                        }
                        VIndex::Aux(aux) => {
                            let new_id = res.old_aux_id_to_new_id[aux];
                            (new_id, *coeff)
                        },
                    }
                }).collect()
            };

            for (a, b, c) in constraints {
                res.constraints.push((
                    remap_lc(a),
                    remap_lc(b),
                    remap_lc(c),
                ));
            }
        }

        res
    }
}

pub fn build_constraint_system_with_inputs_outputs_from_form_cs<Scalar: PrimeField>(
    cs: &FormCS<Scalar>,
    outputs: &[VIndex],
) -> ConstraintSystemWithInputsOutputs<Scalar> {
    let outputs: HashSet<_> = outputs.iter().cloned().collect();
    let num_public_vars = cs.inputs.len();
    let num_aux = cs.aux.len();
    let constraints = cs.constraints.iter().map(|(a, b, c, _)| (a.clone(), b.clone(), c.clone())).collect::<Vec<_>>();

    ConstraintSystemWithInputsOutputs::from_constraint_system(
        &outputs,
        num_public_vars,
        num_aux,
        &constraints,
    )
}


// Copied from ZoKrates/zokrates_circom/src/r1cs.rs
use byteorder::{LittleEndian, WriteBytesExt};
use num_bigint::BigUint;
use std::collections::HashSet;
use std::io::Result;
use std::io::Write;
struct Header {
    pub field_size: u32,
    pub prime_size: Vec<u8>,
    pub n_wires: u32,
    pub n_pub_out: u32,
    pub n_pub_in: u32,
    pub n_prv_in: u32,
    pub n_labels: u64,
    pub n_constraints: u32,
}



fn write_header<W: Write>(writer: &mut W, header: Header) -> Result<()> {
    writer.write_u32::<LittleEndian>(header.field_size)?;
    writer.write_all(&header.prime_size)?;
    writer.write_u32::<LittleEndian>(header.n_wires)?;
    writer.write_u32::<LittleEndian>(header.n_pub_out)?;
    writer.write_u32::<LittleEndian>(header.n_pub_in)?;
    writer.write_u32::<LittleEndian>(header.n_prv_in)?;
    writer.write_u64::<LittleEndian>(header.n_labels)?;
    writer.write_u32::<LittleEndian>(header.n_constraints)?;

    Ok(())
}


fn field_to_big_uint<F: PrimeField + PrimeFieldBits>(input: F) -> BigUint {
    let input_bits = input.to_le_bits();
    let mut sca = BigUint::from(1_usize);
    let mut val = BigUint::from(0_usize);
    for bit in input_bits {
        if bit {
            val += &sca;
        }
        sca *= BigUint::from(2_usize);
    }
    val
}

fn hex_str_to_big_uint(input: &str) -> Option<BigUint> {
    let mut input = input.to_lowercase();
    if input.starts_with("0x") {
        input = input[2..].to_string();
    }
    BigUint::parse_bytes(input.as_bytes(), 16)
}

pub fn write_r1cs<T: PrimeField + PrimeFieldBits, W: Write>(
    writer: &mut W,
    cs: &ConstraintSystemWithInputsOutputs<T>,
) -> Result<()> {
    let t_max_value = hex_str_to_big_uint(T::MODULUS).unwrap();

    let modulo_byte_count = t_max_value.clone().to_bytes_le().len() as u32;

    let n_pub_out = cs.num_outputs as u32;
    let n_pub_in = cs.num_public_inputs as u32;
    let n_prv_in = cs.num_aux as u32;

    let n_vars = cs.num_outputs + cs.num_public_inputs + cs.num_aux;

    let vars = (0..n_vars).collect::<Vec<_>>();

    let constraints = cs.constraints.clone();

    let n_wires = vars.len();

    let header = Header {
        field_size: modulo_byte_count,
        prime_size: t_max_value.to_bytes_le(),
        n_wires: n_wires as u32,
        n_pub_out,
        n_pub_in,
        n_prv_in,
        n_labels: n_wires as u64,
        n_constraints: constraints.len() as u32,
    };

    // magic
    writer.write_all(&[0x72, 0x31, 0x63, 0x73])?;
    // version
    writer.write_u32::<LittleEndian>(1)?;
    // section count
    writer.write_u32::<LittleEndian>(3)?;

    // section type: constraints
    // type
    writer.write_u32::<LittleEndian>(2)?;
    // size: 4 per lc + (32 + 4) per summand
    let size = constraints
        .iter()
        .map(|(a, b, c)| {
            (3 * 4 // for each lc, 4 bytes for its size
                    + (a.len() + b.len() + c.len()) // for each summand
                        * (modulo_byte_count as usize + 4)) // 4 bytes for the signal, `modulo_byte_count` bytes for the coefficient
                as u64
        })
        .sum();
    writer.write_u64::<LittleEndian>(size)?;

    write_constraints(writer, constraints)?;

    // section type: header
    // type
    writer.write_u32::<LittleEndian>(1)?;
    // size
    writer.write_u64::<LittleEndian>(32 + 32)?;

    // header
    write_header(writer, header)?;

    // section type: wire2label
    // type
    writer.write_u32::<LittleEndian>(3)?;
    // size
    writer.write_u64::<LittleEndian>(n_wires as u64 * 8)?;

    write_table(writer, n_vars)?;

    Ok(())
}

fn write_constraints<T: PrimeField + PrimeFieldBits, W: Write>(
    writer: &mut W,
    constraints: Vec<Constraint<T>>,
) -> Result<()> {
    for c in constraints {
        write_lincomb(writer, c.0)?;
        write_lincomb(writer, c.1)?;
        write_lincomb(writer, c.2)?;
    }
    Ok(())
}

fn write_lincomb<T: PrimeField + PrimeFieldBits, W: Write>(writer: &mut W, l: LinComb<T>) -> Result<()> {
    writer.write_u32::<LittleEndian>(l.len() as u32)?;
    for (var, coeff) in l {
        writer.write_u32::<LittleEndian>(var as u32)?;
        let mut res = vec![0u8; 32];

        let coeff = field_to_big_uint(coeff);

        for (value, padded) in coeff.to_bytes_le().iter().zip(res.iter_mut()) {
            *padded = *value;
        }
        writer.write_all(&res)?;
    }
    Ok(())
}

// for now we do not write any signal map
fn write_table<W: Write>(w: &mut W, num_variables: usize) -> Result<()> {
    for i in 0..num_variables {
        w.write_u64::<LittleEndian>(i as u64)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use bellpepper_core::ConstraintSystem;
    
    use zkutil::r1cs_reader;

    use crate::FormCS;

    use super::{build_constraint_system_with_inputs_outputs_from_form_cs, write_r1cs};

    type F = halo2curves::bn256::Fr;

    #[test]
    fn test_cs_to_r1cs_file() {
        let mut cs = FormCS::<F>::new();
        let one = F::from(1);
        let a = cs.alloc_input(|| "a", || Ok(one)).unwrap();
        let b = cs.alloc_input(|| "b", || Ok(one)).unwrap();
        let c = cs.alloc_input(|| "c", || Ok(one)).unwrap();

        cs.enforce(
            || "a * b = c",
            |lc| lc + a,
            |lc| lc + b,
            |lc| lc + c,
        );

        {
            let mut buf = vec![];
            let cs_with_io = build_constraint_system_with_inputs_outputs_from_form_cs(&cs, &[c.0]);
            write_r1cs(&mut buf, &cs_with_io).unwrap();

            let c = Cursor::new(buf);

            let r1cs = r1cs_reader::read(c).unwrap();
            
            assert_eq!(r1cs.header.n_prv_in, 0);
            assert_eq!(r1cs.header.n_pub_in, 2 + 1);
            assert_eq!(r1cs.header.n_pub_out, 1);
            assert_eq!(r1cs.constraints.len(), 1);
            assert_eq!(r1cs.constraints[0].0[0].0, 2);
            assert_eq!(r1cs.constraints[0].1[0].0, 3);
            assert_eq!(r1cs.constraints[0].2[0].0, 0);
        }
        
    }
}
