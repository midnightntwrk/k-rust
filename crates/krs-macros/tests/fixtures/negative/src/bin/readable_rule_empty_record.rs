extern crate renamed_krs as k;

pub struct Machine;

k::rules! {
    for Machine;
    idle: {} => {}; //~ ERROR a machine rule selects at least one cell
}

fn main() {}
