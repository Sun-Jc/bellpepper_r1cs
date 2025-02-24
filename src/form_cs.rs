// ! Adapted from bellpepper/test_cs
use std::collections::HashMap;
use bellpepper_core::{ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};
use ff::PrimeField;

#[allow(dead_code)]
#[derive(Debug)]
enum NamedObject {
    Constraint(usize),
    Var(Variable),
    Namespace,
}

/// Constraint system for testing purposes.
#[derive(Debug)]
pub struct FormCS<Scalar: PrimeField> {
    named_objects: HashMap<String, NamedObject>,
    current_namespace: Vec<String>,
    #[allow(clippy::type_complexity)]
    pub(crate) constraints: Vec<(
        LinearCombination<Scalar>,
        LinearCombination<Scalar>,
        LinearCombination<Scalar>,
        String,
    )>,
    pub(crate) inputs: Vec<(Scalar, String)>,
    pub(crate) aux: Vec<(Scalar, String)>,
}

impl<Scalar: PrimeField> Default for FormCS<Scalar> {
    fn default() -> Self {
        let mut map = HashMap::new();
        map.insert(
            "ONE".into(),
            NamedObject::Var(FormCS::<Scalar>::one()),
        );

        FormCS {
            named_objects: map,
            current_namespace: vec![],
            constraints: vec![],
            inputs: vec![(Scalar::ONE, "ONE".into())],
            aux: vec![],
        }
    }
}

impl<Scalar: PrimeField> FormCS<Scalar> {
    pub fn new() -> Self {
        Default::default()
    }

    fn set_named_obj(&mut self, path: String, to: NamedObject) {
        assert!(
            !self.named_objects.contains_key(&path),
            "tried to create object at existing path: {}",
            path
        );

        self.named_objects.insert(path, to);
    }
}

fn compute_path(ns: &[String], this: &str) -> String {
    assert!(
        !this.chars().any(|a| a == '/'),
        "'/' is not allowed in names"
    );

    if ns.is_empty() {
        return this.to_string();
    }

    let name = ns.join("/");
    format!("{}/{}", name, this)
}

impl<Scalar: PrimeField> ConstraintSystem<Scalar> for FormCS<Scalar> {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.aux.len();
        let path = compute_path(&self.current_namespace, &annotation().into());
        self.aux.push((f()?, path.clone()));
        let var = Variable::new_unchecked(Index::Aux(index));
        self.set_named_obj(path, NamedObject::Var(var));

        Ok(var)
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<Scalar, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.inputs.len();
        let path = compute_path(&self.current_namespace, &annotation().into());
        self.inputs.push((f()?, path.clone()));
        let var = Variable::new_unchecked(Index::Input(index));
        self.set_named_obj(path, NamedObject::Var(var));

        Ok(var)
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LB: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
        LC: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
    {
        let path = compute_path(&self.current_namespace, &annotation().into());
        let index = self.constraints.len();
        self.set_named_obj(path.clone(), NamedObject::Constraint(index));

        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        self.constraints.push((a, b, c, path));
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        let name = name_fn().into();
        let path = compute_path(&self.current_namespace, &name);
        self.set_named_obj(path, NamedObject::Namespace);
        self.current_namespace.push(name);
    }

    fn pop_namespace(&mut self) {
        assert!(self.current_namespace.pop().is_some());
    }

    fn get_root(&mut self) -> &mut <Self as ConstraintSystem<Scalar>>::Root {
        self
    }
}
