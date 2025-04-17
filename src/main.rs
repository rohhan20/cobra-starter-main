use std::env;
use std::fs::File;
use std::io::prelude::*;

/// Enumeration of unary operations in Snek.
#[derive(Debug, Clone)]
enum Op1 { Add1, Sub1 }

/// Enumeration of binary operations in Snek.
#[derive(Debug, Clone)]
enum Op2 { Plus, Minus, Times, Equal, Greater, GreaterEqual, Less, LessEqual }

/// AST for Snek expressions.
#[derive(Debug, Clone)]
enum Expr {
    Number(i64),                  // Numeric literal
    Boolean(bool),                // Boolean literal `true` or `false`
    Input,                        // `input` expression
    Id(String),                   // Identifier
    Let(Vec<(String, Expr)>, Box<Expr>),    // (let (<name> <expr> ... ) <body>)
    UnOp(Op1, Box<Expr>),         // Unary operation, e.g., (add1 <expr>)
    BinOp(Op2, Box<Expr>, Box<Expr>),  // Binary operation, e.g., (+ <e1> <e2>)
    If(Box<Expr>, Box<Expr>, Box<Expr>),    // (if <cond> <then> <else>)
    RepeatUntil(Box<Expr>, Box<Expr>),      // (repeat-until <body> <cond>)
    Set(String, Box<Expr>),       // (set! <name> <expr>)
    Block(Vec<Expr>),             // (block <expr1> <expr2> ... )
}

/// Error type for compile-time errors (with a message).
struct CompileError(String);

// Reserved keywords and symbols that cannot be used as identifiers.
fn is_keyword(name: &str) -> bool {
    matches!(name,
        "true" | "false" | "input" | "let" | "if" | "block" |
        "set!" | "add1" | "sub1" | "repeat-until" | "loop" | "break"
    )
}

//// PARSER ////

struct Parser<'a> {
    src: &'a str,
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(src: &'a str) -> Self {
        Parser { src, pos: 0 }
    }
    fn peek_char(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }
    fn get_char(&mut self) -> Option<char> {
        let ch_opt = self.src[self.pos..].chars().next();
        if let Some(ch) = ch_opt {
            self.pos += ch.len_utf8();
        }
        ch_opt
    }
    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek_char() {
            if c.is_whitespace() { self.get_char(); } else { break; }
        }
    }
    /// Parses the next Snek expression from the input.
    fn parse_expr(&mut self) -> Result<Expr, CompileError> {
        self.skip_whitespace();
        let ch = self.peek_char().ok_or_else(|| CompileError("Unexpected EOF".into()))?;
        if ch == '(' {
            self.get_char();  // consume '('
            self.skip_whitespace();
            // Parse the operator/keyword token after '('
            let token = self.parse_token()?;
            let expr = match token.as_str() {
                "let" => {
                    // Parse bindings list
                    self.skip_whitespace();
                    if self.get_char() != Some('(') {
                        return Err(CompileError("Expected '(' after let".into()));
                    }
                    let mut bindings = Vec::new();
                    loop {
                        self.skip_whitespace();
                        if let Some(')') = self.peek_char() {
                            self.get_char(); // end of bindings
                            break;
                        }
                        if self.get_char() != Some('(') {
                            return Err(CompileError("Expected '(' to start a binding".into()));
                        }
                        self.skip_whitespace();
                        let name = self.parse_token()?;  // parse binding name
                        if is_keyword(&name) {
                            // We don't allow keywords as binding names
                            return Err(CompileError("keyword".into()));
                        }
                        self.skip_whitespace();
                        let val_expr = self.parse_expr()?;
                        self.skip_whitespace();
                        if self.get_char() != Some(')') {
                            return Err(CompileError("Expected ')' after binding expression".into()));
                        }
                        bindings.push((name, val_expr));
                    }
                    self.skip_whitespace();
                    let body = self.parse_expr()?;
                    self.skip_whitespace();
                    if self.get_char() != Some(')') {
                        return Err(CompileError("Expected ')' to close let".into()));
                    }
                    Expr::Let(bindings, Box::new(body))
                }
                "if" => {
                    // (if <cond> <then> <else>)
                    self.skip_whitespace();
                    let cond = self.parse_expr()?;
                    self.skip_whitespace();
                    let then_expr = self.parse_expr()?;
                    self.skip_whitespace();
                    let else_expr = self.parse_expr()?;
                    self.skip_whitespace();
                    if self.get_char() != Some(')') {
                        return Err(CompileError("Expected ')' to close if".into()));
                    }
                    Expr::If(Box::new(cond), Box::new(then_expr), Box::new(else_expr))
                }
                "block" => {
                    // (block e1 e2 ... en)
                    let mut exprs = Vec::new();
                    loop {
                        self.skip_whitespace();
                        if let Some(')') = self.peek_char() {
                            self.get_char();
                            break;
                        }
                        let e = self.parse_expr()?;
                        exprs.push(e);
                    }
                    if exprs.is_empty() {
                        return Err(CompileError("Block must have at least one expression".into()));
                    }
                    Expr::Block(exprs)
                }
                "set!" => {
                    // (set! name expr)
                    self.skip_whitespace();
                    let name = self.parse_token()?;  // target variable name
                    self.skip_whitespace();
                    let val_expr = self.parse_expr()?;
                    self.skip_whitespace();
                    if self.get_char() != Some(')') {
                        return Err(CompileError("Expected ')' to close set!".into()));
                    }
                    Expr::Set(name, Box::new(val_expr))
                }
                "repeat-until" => {
                    // (repeat-until body cond)
                    self.skip_whitespace();
                    let body_expr = self.parse_expr()?;
                    self.skip_whitespace();
                    let cond_expr = self.parse_expr()?;
                    self.skip_whitespace();
                    if self.get_char() != Some(')') {
                        return Err(CompileError("Expected ')' to close repeat-until".into()));
                    }
                    Expr::RepeatUntil(Box::new(body_expr), Box::new(cond_expr))
                }
                "add1" | "sub1" => {
                    // unary operations
                    let op = if token == "add1" { Op1::Add1 } else { Op1::Sub1 };
                    self.skip_whitespace();
                    let expr = self.parse_expr()?;
                    self.skip_whitespace();
                    if self.get_char() != Some(')') {
                        return Err(CompileError(format!("Expected ')' after {} operand", token)));
                    }
                    Expr::UnOp(op, Box::new(expr))
                }
                "+" | "-" | "*" | "<" | ">" | "<=" | ">=" | "=" => {
                    // binary operations
                    let op = match token.as_str() {
                        "+" => Op2::Plus,
                        "-" => Op2::Minus,
                        "*" => Op2::Times,
                        "<" => Op2::Less,
                        ">" => Op2::Greater,
                        "<=" => Op2::LessEqual,
                        ">=" => Op2::GreaterEqual,
                        "=" => Op2::Equal,
                        _ => unreachable!(),
                    };
                    self.skip_whitespace();
                    let e1 = self.parse_expr()?;
                    self.skip_whitespace();
                    let e2 = self.parse_expr()?;
                    self.skip_whitespace();
                    if self.get_char() != Some(')') {
                        return Err(CompileError("Expected ')' to close binary op".into()));
                    }
                    Expr::BinOp(op, Box::new(e1), Box::new(e2))
                }
                _ => {
                    // If the token is not a recognized form, it's an error (Snek has no function calls).
                    return Err(CompileError(format!("Unknown form: {}", token)));
                }
            };
            Ok(expr)
        } else {
            // Not a parenthesized expression. It could be a literal or identifier.
            let token = self.parse_token()?;
            if let Ok(num) = token.parse::<i64>() {
                Ok(Expr::Number(num))
            } else if token == "true" {
                Ok(Expr::Boolean(true))
            } else if token == "false" {
                Ok(Expr::Boolean(false))
            } else if token == "input" {
                Ok(Expr::Input)
            } else {
                Ok(Expr::Id(token))
            }
        }
    }
    /// Parses the next token (identifier, number, or operator) from the input.
    fn parse_token(&mut self) -> Result<String, CompileError> {
        self.skip_whitespace();
        let mut token = String::new();
        let ch = self.peek_char().ok_or_else(|| CompileError("Unexpected EOF".into()))?;
        // Handle numeric literal (including a negative sign attached to number)
        if ch.is_digit(10) || (ch == '-' && {
            // look ahead: '-' followed by a digit means a negative number literal, not the subtraction operator
            let mut it = self.src[self.pos..].chars();
            it.next();  // consume '-'
            matches!(it.next(), Some(d) if d.is_digit(10))
        }) {
            if ch == '-' { token.push(ch); self.get_char(); }
            while let Some(d) = self.peek_char() {
                if d.is_digit(10) { token.push(d); self.get_char(); }
                else { break; }
            }
            return Ok(token);
        }
        // Handle operator symbols and identifiers
        if "+-*<>=!".contains(ch) {
            // Possible multi-character operators (<=, >=)
            let first = self.get_char().unwrap();
            token.push(first);
            if (first == '<' || first == '>') && self.peek_char() == Some('=') {
                token.push(self.get_char().unwrap());
            } else if first == '!' {
                // '!' is only expected as part of "set!" token, which we handle in parse_expr by matching exact "set!".
                // If we see a lone '!' here, that's an error (or part of invalid identifier).
            }
            return Ok(token);
        }
        // Handle identifiers (alphabetic start, then alphanumeric/underscore/'!'/'?')
        if ch.is_alphabetic() || ch == '_' {
            while let Some(c) = self.peek_char() {
                if c.is_alphanumeric() || c == '_' || c == '!' || c == '?' || c == '-' {
                    token.push(c);
                    self.get_char();
                } else { break; }
            }
            return Ok(token);
        }
        Err(CompileError(format!("Unexpected character '{}'", ch)))
    }
}

//// STATIC SEMANTIC CHECKS (TYPE CHECKING) ////

#[derive(Debug, Clone, PartialEq)]
enum Type { Number, Boolean }

/// Recursively type-checks an expression. Returns its type on success or a CompileError on failure.
fn type_check_expr(expr: &Expr, env: &mut Vec<(String, Type)>) -> Result<Type, CompileError> {
    use Type::*;
    match expr {
        Expr::Number(n) => {
            // Check if the number is within the valid range for Snek
            if *n > 4611686018427387903 || *n < -4611686018427387904 {
                return Err(CompileError("Invalid number literal: out of range".into()));
            }
            Ok(Number)
        },
        Expr::Boolean(_) => Ok(Boolean),
        Expr::Input => Ok(Number),  // `input` is always a number (by spec, must be an integer CLI argument)
        Expr::Id(name) => {
            // Look up variable in environment (from innermost scope outward)
            for (n, t) in env.iter().rev() {
                if n == name { return Ok(t.clone()); }
            }
            // Not found in any enclosing scope:
            Err(CompileError(format!("Unbound variable identifier {}", name)))
        }
        Expr::UnOp(op, e) => {
            let t = type_check_expr(e, env)?;
            if t != Number {
                return Err(CompileError("type mismatch".into())); // add1/sub1 require number
            }
            Ok(Number)
        }
        Expr::BinOp(op, e1, e2) => {
            let t1 = type_check_expr(e1, env)?;
            let t2 = type_check_expr(e2, env)?;
            match op {
                Op2::Plus | Op2::Minus | Op2::Times 
                    => {
                        // arithmetic ops require both operands numbers
                        if t1 != Number || t2 != Number {
                            return Err(CompileError("type mismatch".into()));
                        }
                        Ok(Number)
                    }
                Op2::Equal => {
                    // '=' requires both operands have the same type (either both number or both boolean)
                    if t1 != t2 {
                        return Err(CompileError("type mismatch".into()));
                    }
                    Ok(Boolean)
                }
                Op2::Less | Op2::Greater | Op2::LessEqual | Op2::GreaterEqual 
                    => {
                        // comparison ops require numbers
                        if t1 != Number || t2 != Number {
                            return Err(CompileError("type mismatch".into()));
                        }
                        Ok(Boolean)
                    }
            }
        }
        Expr::If(cond, then_e, else_e) => {
            let tcond = type_check_expr(cond, env)?;
            if tcond != Boolean {
                return Err(CompileError("type mismatch".into()));  // condition must be boolean
            }
            let t_then = type_check_expr(then_e, env)?;
            let t_else = type_check_expr(else_e, env)?;
            if t_then != t_else {
                // Require then/else to have same type (to decide one flag for printing)
                return Err(CompileError("type mismatch".into()));
            }
            Ok(t_then)
        }
        Expr::Let(bindings, body) => {
            // Check for duplicate names in this binding list
            let mut seen = std::collections::HashSet::new();
            // Evaluate each binding expression in the *outer* environment
            let mut types = Vec::new();
            for (name, val_expr) in bindings {
                if !seen.insert(name) {
                    return Err(CompileError("Duplicate binding".into()));
                }
                if is_keyword(name) {
                    return Err(CompileError("keyword".into()));
                }
                let t = type_check_expr(val_expr, env)?;
                types.push((name.clone(), t));
            }
            // Extend environment with new bindings for the body
            for (name, t) in &types {
                env.push((name.clone(), t.clone()));
            }
            let result_type = type_check_expr(body, env)?;
            // Pop the bindings after checking the body
            for _ in types { env.pop(); }
            Ok(result_type)
        }
        Expr::Set(name, e) => {
            // Assignment target must exist in some enclosing scope
            let mut found_type = None;
            for (n, t) in env.iter().rev() {
                if n == name {
                    found_type = Some(t.clone());
                    break;
                }
            }
            if found_type.is_none() {
                return Err(CompileError(format!("Unbound variable identifier {}", name)));
            }
            if is_keyword(name) {
                return Err(CompileError("keyword".into()));
            }
            let target_type = found_type.unwrap();
            let val_type = type_check_expr(e, env)?;
            if target_type != val_type {
                return Err(CompileError("type mismatch".into()));
            }
            Ok(val_type)
        }
        Expr::Block(exprs) => {
            let mut result_type = Type::Number;
            for (i, e) in exprs.iter().enumerate() {
                let t = type_check_expr(e, env)?;
                result_type = t;
            }
            Ok(result_type)
        }
        Expr::RepeatUntil(body, cond) => {
            let t_body = type_check_expr(body, env)?;
            let t_cond = type_check_expr(cond, env)?;
            if t_cond != Boolean {
                return Err(CompileError("type mismatch".into()));
            }
            // The loop expression evaluates to the value of the body when the loop exits
            Ok(t_body)
        }
    }
}

//// CODE GENERATION ////

struct CodeGenContext {
    label_count: u32,
    next_slot: usize,  // next stack slot index to allocate (1 is reserved for RBX save)
}
impl CodeGenContext {
    fn new() -> Self {
        CodeGenContext { label_count: 0, next_slot: 1 }
    }
    fn new_label(&mut self) -> String {
        let lbl = format!("label_{}", self.label_count);
        self.label_count += 1;
        lbl
    }
}

/// Recursively generates assembly code for an expression. 
/// `env` maps variable names to their stack slot indices (1-based: 1 is RBP-8, 2 is RBP-16, etc.).
fn compile_expr(expr: &Expr, env: &mut Vec<(String, usize)>, ctx: &mut CodeGenContext) -> String {
    use Op2::*;
    use Type::*;
    let mut code = String::new();
    match expr {
        Expr::Number(n) => {
            // Tag the 64-bit integer by shifting left (LSB=0)
            let tagged_val = (*n as i128) << 1; 
            let tagged_val = tagged_val as i64;
            code += &format!("  mov rax, {}\n", tagged_val);
        }
        Expr::Boolean(b) => {
            let val = if *b { 3 } else { 1 };  // true=3 (0b11), false=1 (0b01)
            code += &format!("  mov rax, {}\n", val);
        }
        Expr::Input => {
            // The input value is already passed in RDI (as 64-bit tagged integer)
            code += "  mov rax, rdi\n";
        }
        Expr::Id(name) => {
            // Load the value from its stack slot into RAX
            if let Some((_, slot)) = env.iter().rev().find(|(n, _)| n == name) {
                code += &format!("  mov rax, [rbp-{}]\n", slot * 8);
            } else {
                // (Should not happen due to type checking)
                code += "  mov rax, 0\n";
            }
        }
        Expr::UnOp(op, e) => {
            code += &compile_expr(e, env, ctx);
            match op {
                Op1::Add1 => code += "  add rax, 2\n",   // adding 1 to actual => add 2 to tagged
                Op1::Sub1 => code += "  sub rax, 2\n",
            }
            // Check for overflow (if adding 2 to max tagged int overflowed)
            let overflow_lbl = ctx.new_label();
            let cont_lbl = ctx.new_label();
            code += &format!("  jo {}\n", overflow_lbl);
            code += &format!("  jmp {}\n", cont_lbl);
            code += &format!("{}:\n", overflow_lbl);
            code += "  mov rdi, 1\n";          // error code 1 = overflow
            code += "  call snek_error\n";
            code += &format!("{}:\n", cont_lbl);
        }
        Expr::BinOp(op, e1, e2) => {
            match op {
                Plus | Minus | Times => {
                    // Evaluate left operand
                    code += &compile_expr(e1, env, ctx);
                    // Save left value in RBX
                    code += "  mov rbx, rax\n";
                    // Evaluate right operand (result in RAX)
                    code += &compile_expr(e2, env, ctx);
                    match op {
                        Op2::Plus   => code += "  add rax, rbx\n",
                        Op2::Minus  => {
                            // (minus) result = left - right: we have left in RBX, right in RAX
                            code += "  mov rcx, rax\n";   // preserve right
                            code += "  mov rax, rbx\n";   // move left into RAX
                            code += "  sub rax, rcx\n";
                        }
                        Op2::Times  => {
                            // Multiply left * right: since both are tagged (even), do (rax >>=1) * rbx
                            code += "  sar rax, 1\n";     // divide right by 2 (remove tag) 
                            code += "  imul rax, rbx\n";  // rax = rax * rbx  (rbx still tagged: effectively 2a * b = 2ab)
                        }
                        _ => {}
                    }
                    // Overflow check for arithmetic
                    let overflow_lbl = ctx.new_label();
                    let cont_lbl = ctx.new_label();
                    code += &format!("  jo {}\n", overflow_lbl);
                    code += &format!("  jmp {}\n", cont_lbl);
                    code += &format!("{}:\n", overflow_lbl);
                    code += "  mov rdi, 1\n";
                    code += "  call snek_error\n";
                    code += &format!("{}:\n", cont_lbl);
                }
                Equal | Less | Greater | LessEqual | GreaterEqual => {
                    // Evaluate both operands
                    code += &compile_expr(e1, env, ctx);
                    code += "  mov rbx, rax\n";        // save left
                    code += &compile_expr(e2, env, ctx);
                    match op {
                        Op2::Equal => {
                            // Compare full 64-bit tagged values
                            code += "  cmp rax, rbx\n";
                            let eq_lbl = ctx.new_label();
                            let done_lbl = ctx.new_label();
                            code += &format!("  je {}\n", eq_lbl);
                            // Not equal -> result = false (1)
                            code += "  mov rax, 1\n";
                            code += &format!("  jmp {}\n", done_lbl);
                            // Equal -> result = true (3)
                            code += &format!("{}:\n", eq_lbl);
                            code += "  mov rax, 3\n";
                            code += &format!("{}:\n", done_lbl);
                        }
                        // For ordering comparisons, compare as untagged signed integers
                        Op2::Less | Op2::Greater | Op2::LessEqual | Op2::GreaterEqual => {
                            code += "  mov rcx, rax\n";  // rcx = right
                            code += "  mov rax, rbx\n";  // rax = left
                            code += "  sar rax, 1\n";    // untag left (arith shift preserves sign)
                            code += "  sar rcx, 1\n";    // untag right
                            code += "  cmp rax, rcx\n";
                            let true_lbl = ctx.new_label();
                            let done_lbl = ctx.new_label();
                            match op {
                                Op2::Less        => code += &format!("  jl {}\n", true_lbl),
                                Op2::Greater     => code += &format!("  jg {}\n", true_lbl),
                                Op2::LessEqual   => code += &format!("  jle {}\n", true_lbl),
                                Op2::GreaterEqual=> code += &format!("  jge {}\n", true_lbl),
                                _ => {}
                            }
                            // If comparison is false:
                            code += "  mov rax, 1\n";    // false (1)
                            code += &format!("  jmp {}\n", done_lbl);
                            // If comparison is true:
                            code += &format!("{}:\n", true_lbl);
                            code += "  mov rax, 3\n";
                            code += &format!("{}:\n", done_lbl);
                        }
                        _ => {}
                    }
                }
            }
        }
        Expr::If(cond, then_e, else_e) => {
            // Compute condition
            code += &compile_expr(cond, env, ctx);
            let else_lbl = ctx.new_label();
            let end_lbl = ctx.new_label();
            // If condition is false (== 1), jump to else branch
            code += "  cmp rax, 1\n";
            code += &format!("  je {}\n", else_lbl);
            // Then-branch
            code += &compile_expr(then_e, env, ctx);
            code += &format!("  jmp {}\n", end_lbl);
            // Else-branch
            code += &format!("{}:\n", else_lbl);
            code += &compile_expr(else_e, env, ctx);
            code += &format!("{}:\n", end_lbl);
        }
        Expr::Let(bindings, body) => {
            // Evaluate each binding and store its value on stack
            for (name, val_expr) in bindings {
                code += &compile_expr(val_expr, env, ctx);
                // Allocate a new stack slot for this binding
                let slot = ctx.next_slot;
                ctx.next_slot += 1;
                code += &format!("  mov [rbp-{}], rax\n", slot * 8);
                env.push((name.clone(), slot));
            }
            // Compile the body with the extended environment
            code += &compile_expr(body, env, ctx);
            // Pop the bindings out of the environment
            for _ in bindings { env.pop(); }
        }
        Expr::Set(name, e) => {
            code += &compile_expr(e, env, ctx);
            // Find the stack slot for the variable and store the new value
            if let Some((_, slot)) = env.iter().rev().find(|(n, _)| n == name) {
                code += &format!("  mov [rbp-{}], rax\n", slot * 8);
            }
        }
        Expr::Block(exprs) => {
            for (i, sub_expr) in exprs.iter().enumerate() {
                code += &compile_expr(sub_expr, env, ctx);
                // The value of non-last expressions is unused (overwritten by next expr)
            }
        }
        Expr::RepeatUntil(body, cond) => {
            // Allocate a scratch slot to save the body result each iteration
            let scratch_slot = ctx.next_slot;
            ctx.next_slot += 1;
            let loop_start_lbl = ctx.new_label();
            code += &format!("{}:\n", loop_start_lbl);
            // Evaluate loop body and save its result
            code += &compile_expr(body, env, ctx);
            code += &format!("  mov [rbp-{}], rax\n", scratch_slot * 8);
            // Evaluate condition
            code += &compile_expr(cond, env, ctx);
            // If condition is false (value = 1), loop again; if true (3), break
            code += "  cmp rax, 3\n";
            code += &format!("  jne {}\n", loop_start_lbl);
            // On break: restore the last body result as the loop's value
            code += &format!("  mov rax, [rbp-{}]\n", scratch_slot * 8);
        }
    }
    code
}

fn main() -> std::io::Result<()> {
    // Read input and output file paths from CLI arguments
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: {} <input_file> <output_file>", args.get(0).unwrap_or(&"compiler".to_string()));
        std::process::exit(1);
    }
    let in_name = &args[1];
    let out_name = &args[2];
    // Read the source program
    let mut infile = File::open(in_name)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("Failed to open {}: {}", in_name, e)))?;
    let mut input_code = String::new();
    infile.read_to_string(&mut input_code)?;
    // Parse the program into an AST
    let mut parser = Parser::new(&input_code);
    let program = match parser.parse_expr() {
        Ok(expr) => {
            parser.skip_whitespace();
            if parser.peek_char().is_some() {
                eprintln!("Error: syntax error");
                std::process::exit(1);
            }
            expr
        }
        Err(err) => {
            eprintln!("Error: {}", err.0);
            std::process::exit(1);
        }
    };
    // Type-check the AST
    let mut type_env = Vec::new();
    let prog_type = match type_check_expr(&program, &mut type_env) {
        Ok(t) => t,
        Err(err) => {
            eprintln!("Error: {}", err.0);
            std::process::exit(1);
        }
    };
    // Generate assembly code for the AST
    let mut ctx = CodeGenContext::new();
    let mut env_codegen = Vec::new();
    let code_body = compile_expr(&program, &mut env_codegen, &mut ctx);
    // Compute total stack space needed (in 8-byte slots). 
    // ctx.next_slot is the next free slot index, so the highest used index is next_slot-1.
    let mut total_slots = ctx.next_slot;
    if total_slots % 2 != 0 {
        // Ensure even number of slots for 16-byte alignment
        total_slots += 1;
    }
    let total_bytes = total_slots * 8;
    // Build the full assembly program string
    let mut asm_program = String::new();
    asm_program.push_str("section .text\n");
    asm_program.push_str("extern snek_error\n");
    asm_program.push_str("extern snek_print\n");
    asm_program.push_str("global our_code_starts_here\n");
    asm_program.push_str("our_code_starts_here:\n");
    asm_program.push_str("  push rbp\n");
    asm_program.push_str("  mov rbp, rsp\n");
    asm_program.push_str(&format!("  sub rsp, {}\n", total_bytes));
    // Save callee-saved RBX (slot 1)
    asm_program.push_str("  mov [rbp-8], rbx\n");
    // Generated code for the program body
    asm_program.push_str(&code_body);
    // Call snek_print with the result in RAX. Determine flag from static type.
    match prog_type {
        Type::Boolean => {
            asm_program.push_str("  mov rdi, rax\n");
            asm_program.push_str("  mov rsi, 1\n");   // flag = 1 for boolean
        }
        Type::Number => {
            asm_program.push_str("  mov rdi, rax\n");
            asm_program.push_str("  mov rsi, 0\n");   // flag = 0 for number
        }
    }
    asm_program.push_str("  call snek_print\n");
    // Epilogue: restore RBX and RBP, return
    asm_program.push_str("  mov rbx, [rbp-8]\n");
    asm_program.push_str("  mov rsp, rbp\n");
    asm_program.push_str("  pop rbp\n");
    asm_program.push_str("  ret\n");
    // Write assembly to output file
    let mut outfile = File::create(out_name)?;
    outfile.write_all(asm_program.as_bytes())?;
    Ok(())
}
