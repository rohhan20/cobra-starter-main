use std::env;

#[link(name = "our_code")]
extern "C" {
    // The \x01 here is an undocumented feature of LLVM that ensures
    // it does not add an underscore in front of the name.
    // Courtesy of Max New (https://maxsnew.com/teaching/eecs-483-fa22/hw_adder_assignment.html)
    #[link_name = "\x01our_code_starts_here"]
    fn our_code_starts_here(input: i64) -> i64;
}

#[export_name = "\x01snek_error"]
pub extern "C" fn snek_error(errcode: i64) {
    // Error codes:
    // 1: Overflow
    // 2: Type mismatch
    // 3: Unbound variable
    // etc...
    
    match errcode {
        1 => eprintln!("Error: overflow"),
        2 => eprintln!("Error: type mismatch"),
        3 => eprintln!("Error: unbound variable"),
        _ => eprintln!("Error: unknown error code {}", errcode),
    }
    std::process::exit(1);
}

#[export_name = "\x01snek_print"]
pub extern "C" fn snek_print(val: i64, is_boolean: i64) {
    if is_boolean != 0 {
        if val == 1 {
            println!("true");
        } else {
            println!("false");
        }
    } else {
        println!("{}", val);
    }
}

fn parse_input() -> i64 {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        return 0; // Default to 0 if no argument provided
    }
    
    match args[1].parse::<i64>() {
        Ok(n) => n,
        Err(_) => {
            eprintln!("Error: Invalid input - expected a 64-bit signed integer");
            std::process::exit(1);
        }
    }
}

fn main() {
    let input = parse_input();
    let result = unsafe { our_code_starts_here(input) };
    // For now we'll assume all results are numbers
    // This will need to be updated once you implement type tags
    snek_print(result, 0);
}
