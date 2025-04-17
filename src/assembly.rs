pub fn compile_program(e: &Expr, result_type: &Type) -> String {
    let mut context = Context {
        si: 2,
        env: HashMap::new(),
        label_count: 0,
    };
    
    // Generate assembly instructions for the expression
    let instrs = compile_expr(e, &mut context);
    
    // Embed instructions in the template
    format!(
        "
section .text
extern snek_error
extern snek_print
global our_code_starts_here
our_code_starts_here:
    mov r15, rdi  ; Save input in r15
    
    ; Allocate stack space
    sub rsp, 8
    
    ; Your generated code here
    {}
    
    ; Check if result is a boolean or number
    mov rsi, {}   ; 0 for number, 1 for boolean
    mov rdi, rax  ; Move result to first argument
    call snek_print
    
    add rsp, 8
    ret
        ",
        instrs,
        if *result_type == Type::Boolean { "1" } else { "0" }
    )
}