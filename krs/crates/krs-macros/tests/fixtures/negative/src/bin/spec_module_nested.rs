use renamed_krs as k;

#[k::spec_module(imports = [crate])]
mod outer {
    #[k::spec_module(imports = [super::outer])] //~ ERROR spec modules do not nest
    mod inner {}
}

fn main() {}
