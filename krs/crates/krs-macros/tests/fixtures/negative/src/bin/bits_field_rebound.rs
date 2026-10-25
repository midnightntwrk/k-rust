use renamed_krs as k;
use renamed_krs::builtin::Int;

#[k::function(total, internal)]
pub fn Code(value: k::Term<Int>) -> k::Term<Int>;

#[k::equation]
fn code_let(k::term![Code(k::bits!("1yy"))]: k::Term<Int>) -> k::Term<Int> {
    {
        let y = 1; //~ ERROR `y` is a field of the sentence's bit template and cannot be bound again here
        y
    }
}

fn main() {}
