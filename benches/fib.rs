use criterion::{Criterion, criterion_group, criterion_main};
use std::cell::RefCell;
use std::rc::Rc;

use simian_rs::backend::compiler::Compiler;
use simian_rs::frontend::{Lexer, Parser};
use simian_rs::runtime::{Object, evaluator::eval_program, object::Enviroment, vm::VM};

fn configure_criterion() -> Criterion {
    Criterion::default().sample_size(10)
}

const PROGRAM: &str = r#"
let fibonacci = fn(x) {
    if (x == 0) {
        0
    } else {
        if (x == 1) {
            return 1;
        } else {
            fibonacci(x - 1) + fibonacci(x - 2);
        }
    }
};
fibonacci(35);
"#;

pub fn run_evaluator(c: &mut Criterion) {
    c.bench_function("eval", |b| {
        b.iter(|| {
            let mut lexer = Lexer::new(PROGRAM);
            let mut parser = Parser::new(&mut lexer);
            let program = parser.parse_program().unwrap();

            let env = Rc::new(RefCell::new(Enviroment::new()));
            let result = eval_program(&program, &env).unwrap();
            assert_eq!(
                result,
                Object::Integer(9227465),
            );
        })
    });
}

pub fn run_vm(c: &mut Criterion) {
    c.bench_function("vm", |b| {
        b.iter(|| {
            let mut lexer = Lexer::new(PROGRAM);
            let mut parser = Parser::new(&mut lexer);
            let program = parser.parse_program().unwrap();

            let mut compiler = Compiler::new();
            compiler.compile_program(&program).unwrap();

            let mut vm = VM::new(compiler.bytecode());
            vm.run().unwrap();
            let result = vm.last_popped_stack_element().clone();
            assert_eq!(
                result,
                Object::Integer(9227465),
            );
        })
    });
}

criterion_group! {
    name = fib_benches;
    config = configure_criterion();
    targets = run_evaluator, run_vm
}
criterion_main!(fib_benches);
