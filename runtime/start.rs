use std::env;

#[link(name = "our_code")]
extern "C" {
    // Link to the compiled assembly function
    #[link_name = "\x01our_code_starts_here"]
    fn our_code_starts_here(input: u64) -> u64;
}

#[export_name = "\x01snek_error"]
pub extern "C" fn snek_error(errcode: i64) {
    // Print an error message and exit with nonzero status
    match errcode {
        1 => eprintln!("overflow"),        // numeric overflow error
        2 => eprintln!("invalid input"),   // non-integer or out-of-range input
        _ => eprintln!("an error occurred {errcode}"),
    }
    std::process::exit(1);
}

#[export_name = "\x01snek_print"]
pub extern "C" fn snek_print(value: i64, type_flag: u64) {
    // Determine type from flag and print accordingly
    if type_flag == 1 {
        // Boolean: value should be 1 (false) or 3 (true)
        if value == 1 {
            println!("false");
        } else {
            println!("true");
        }
    } else {
        // Number: the value is tagged (LSB=0), so shift right to get the integer
        let n = (value >> 1) as i64;
        println!("{}", n);
    }
}

fn parse_input(input: &str) -> u64 {
    // Parse command-line input string to a 64-bit signed integer
    match input.parse::<i64>() {
        Ok(n) => {
            // If input integer is outside the allowed range for Snek (±2^62)
            if n > 4611686018427387903 || n < -4611686018427387904 {
                snek_error(1);  // treat as overflow error
            }
            // Tag the integer (shift left 1 to make room for LSB=0 tag)
            (n as u64) << 1
        }
        Err(_) => {
            // Not a valid integer
            snek_error(2);
            0  // (unreachable, snek_error exits)
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    // If no argument is provided, default input is 0
    let input_str = if args.len() == 2 { &args[1] } else { "0" };
    let input_val = parse_input(input_str);
    // Call the compiled function (unsafe because it's extern)
    unsafe {
        our_code_starts_here(input_val);
    }
    // The our_code_starts_here function will have already called snek_print 
    // to print the result, so we don't print anything here.
}
