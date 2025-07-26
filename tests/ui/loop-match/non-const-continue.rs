// Test that `#[const_continue]` attribute can only be placed on constants.

#![allow(incomplete_features)]
#![feature(loop_match)]
#![crate_type = "lib"]

fn test(mut state: u8) {
    #[loop_match]
    loop {
        state = 'blk: {
            match state {
                0 => {
                    #[const_continue]
                    break 'blk state;
                    //~^ ERROR the value of this `#[const_continue]` is not a constant
                }

                _ => unreachable!(),
            }
        }
    }
}
