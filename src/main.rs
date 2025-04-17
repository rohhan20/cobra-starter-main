use std::env;
use std::fs::File;
use std::io::prelude::*;
use sexp::*;
use sexp::Atom::*;
use std::collections::HashMap;

#[derive(Debug)]
enum Val {
    Reg(String),
    Imm(i64),
    RegOffset(String, i64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Op1 {
    Add1,
    Sub1,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Op2 {
    Plus,
    Minus,
    Times,
    Equal,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
}

#[derive(Debug, Clone)]
enum Expr {
    Number(i64),
    Boolean(bool),
    Id(String),
    Let(Vec<(String, Box<Expr>)>, Box<Expr>),
    UnOp(Op1, Box<Expr>),
    BinOp(Op2, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    RepeatUntil(Box<Expr>, Box<Expr>),
    Set(String, Box<Expr>),
    Block(Vec<Expr>),
    Input,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Type {
    Number,
    Boolean,
}

// Constants and reserved keywords
const RESERVED_KEYWORDS: &[&str] = &["let", "add1", "sub1", "true", "false", "if", "block", "input", "set!", "repeat-until"];

// Error reporting
fn compile_error(msg: &str) -> ! {
    eprintln!("{}", msg);
    std::process::exit(1);
}

fn parse_expr(s: &Sexp) -> Expr {
    match s {
        Sexp::Atom(I(n)) => Expr::Number(*n as i64),
        Sexp::Atom(S(name)) if name == "true" => Expr::Boolean(true),
        Sexp::Atom(S(name)) if name == "false" => Expr::Boolean(false),
        Sexp::Atom(S(name)) if name == "input" => Expr::Input,
        Sexp::Atom(S(name)) => Expr::Id(name.to_string()),
        Sexp::List(vec) => parse_compound_expr(vec),
        _ => compile_error("Invalid expression"),
    }
}

fn parse_compound_expr(vec: &[Sexp]) -> Expr {
    if vec.is_empty() {
        compile_error("Expected non-empty list");
    }
    match &vec[0] {
        Sexp::Atom(S(op)) if op == "let" => parse_let(&vec[1..]),
        Sexp::Atom(S(op)) if op == "add1" => parse_unop(Op1::Add1, &vec[1..]),
        Sexp::Atom(S(op)) if op == "sub1" => parse_unop(Op1::Sub1, &vec[1..]),
        Sexp::Atom(S(op)) if op == "+" => parse_binop(Op2::Plus, &vec[1..]),
        Sexp::Atom(S(op)) if op == "-" => parse_binop(Op2::Minus, &vec[1..]),
        Sexp::Atom(S(op)) if op == "*" => parse_binop(Op2::Times, &vec[1..]),
        Sexp::Atom(S(op)) if op == "=" => parse_binop(Op2::Equal, &vec[1..]),
        Sexp::Atom(S(op)) if op == ">" => parse_binop(Op2::Greater, &vec[1..]),
        Sexp::Atom(S(op)) if op == ">=" => parse_binop(Op2::GreaterEqual, &vec[1..]),
        Sexp::Atom(S(op)) if op == "<" => parse_binop(Op2::Less, &vec[1..]),
        Sexp::Atom(S(op)) if op == "<=" => parse_binop(Op2::LessEqual, &vec[1..]),
        Sexp::Atom(S(op)) if op == "if" => parse_if(&vec[1..]),
        Sexp::Atom(S(op)) if op == "block" => parse_block(&vec[1..]),
        Sexp::Atom(S(op)) if op == "set!" => parse_set(&vec[1..]),
        Sexp::Atom(S(op)) if op == "repeat-until" => parse_repeat_until(&vec[1..]),
        _ => compile_error(&format!("Unknown operator: {:?}", vec[0])),
    }
}

// Parsing functions for each expression type
fn parse_let(args: &[Sexp]) -> Expr {
    // TODO: Implement let parsing
    todo!()
}

fn parse_unop(op: Op1, args: &[Sexp]) -> Expr {
    if args.len() != 1 {
        compile_error(&format!("Expected 1 argument for unary operator, got {}", args.len()));
    }
    let e = parse_expr(&args[0]);
    Expr::UnOp(op, Box::new(e))
}

fn parse_binop(op: Op2, args: &[Sexp]) -> Expr {
    if args.len() != 2 {
        compile_error(&format!("Expected 2 arguments for binary operator, got {}", args.len()));
    }
    let e1 = parse_expr(&args[0]);
    let e2 = parse_expr(&args[1]);
    Expr::BinOp(op, Box::new(e1), Box::new(e2))
}

fn parse_if(args: &[Sexp]) -> Expr {
    if args.len() != 3 {
        compile_error(&format!("Expected 3 arguments for if, got {}", args.len()));
    }
    let cond = parse_expr(&args[0]);
    let then_expr = parse_expr(&args[1]);
    let else_expr = parse_expr(&args[2]);
    Expr::If(Box::new(cond), Box::new(then_expr), Box::new(else_expr))
}

fn parse_block(args: &[Sexp]) -> Expr {
    if args.is_empty() {
        compile_error("Block requires at least one expression");
    }
    Expr::Block(args.iter().map(parse_expr).collect())
}

fn parse_set(args: &[Sexp]) -> Expr {
    if args.len() != 2 {
        compile_error(&format!("Expected 2 arguments for set!, got {}", args.len()));
    }
    match &args[0] {
        Sexp::Atom(S(name)) => {
            let val = parse_expr(&args[1]);
            Expr::Set(name.to_string(), Box::new(val))
        }
        _ => compile_error("First argument to set! must be an identifier"),
    }
}

fn parse_repeat_until(args: &[Sexp]) -> Expr {
    if args.len() != 2 {
        compile_error(&format!("Expected 2 arguments for repeat-until, got {}", args.len()));
    }
    let body = parse_expr(&args[0]);
    let condition = parse_expr(&args[1]);
    Expr::RepeatUntil(Box::new(body), Box::new(condition))
}

struct TypeChecker {
    env: Vec<HashMap<String, Type>>,
}

impl TypeChecker {
    fn new() -> Self {
        TypeChecker { env: vec![HashMap::new()] }
    }

    fn type_check(&mut self, e: &Expr) -> Type {
        // TODO: Implement type checking
        match e {
            Expr::Number(_) => Type::Number,
            Expr::Boolean(_) => Type::Boolean,
            // Add other cases
            _ => todo!("Implement type checking for all expressions"),
        }
    }
}

fn compile_to_assembly(expr: &Expr, result_type: Type) -> String {
    // TODO: Implement assembly code generation
    todo!("Implement code generation")
}

fn compile(program: &str, outfile: &str) -> std::io::Result<()> {
    // Parse the program
    let parsed = match parse(program) {
        Ok(expr) => expr,
        Err(e) => compile_error(&format!("Parse error: {}", e)),
    };
    
    // Parse into AST
    let expr = parse_expr(&parsed);
    
    // Type check
    let mut type_checker = TypeChecker::new();
    let result_type = type_checker.type_check(&expr);
    
    // Generate assembly
    let asm = compile_to_assembly(&expr, result_type);
    
    // Write to output file
    let mut file = File::create(outfile)?;
    file.write_all(asm.as_bytes())?;
    Ok(())
}

fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: {} <input_file> <output_file>", args[0]);
        std::process::exit(1);
    }

    let in_name = &args[1];
    let out_name = &args[2];
    
    let mut in_file = File::open(in_name)?;
    let mut contents = String::new();
    in_file.read_to_string(&mut contents)?;
    
    compile(&contents, out_name)
}

fn check_keywords(name: &str) {
    if RESERVED_KEYWORDS.contains(&name) {
        compile_error(&format!("Cannot use keyword '{}' as an identifier", name));
    }
}

// Parse the input S-expression format
fn parse(expr: &str) -> Result<Sexp, String> {
    match parser::parse(expr) {
        Ok(expr) => Ok(expr),
        Err(_) => Err("Invalid S-expression".to_string()),
    }
}